"""Native downloads and RPM reads are bounded and never install package hooks."""
import hashlib
import io
import lzma
from pathlib import Path
import stat
import struct
import tempfile
import unittest
from unittest import mock

from stlmc.cli import native_archive


LIBRARY = 'usr/lib64/libcudd-3.0.0.so.0.0.0'
LICENSE = 'usr/share/licenses/cudd/LICENSE'


def cpio(entries, trailer=True):
    content = bytearray()
    records = list(entries) + ([('TRAILER!!!', b'', 0, 1)] if trailer else [])
    for name, data, mode, links in records:
        encoded = name.encode() + b'\0'
        fields = [1, mode, 0, 0, links, 0, len(data), 0, 0, 0, 0, len(encoded), 0]
        content.extend(b'070701' + ''.join('{:08x}'.format(x) for x in fields).encode())
        content.extend(encoded)
        content.extend(b'\0' * (-len(content) % 4))
        content.extend(data)
        content.extend(b'\0' * (-len(content) % 4))
    return bytes(content)


def rpm(payload):
    lead = b'\xed\xab\xee\xdb\x03' + b'\0' * 91
    header = b'\x8e\xad\xe8\x01\0\0\0\0' + struct.pack('>II', 0, 0)
    return lead + header + header + lzma.compress(payload)


class NativeArchiveTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.archive = self.root / 'package.rpm'
        self.destination = self.root / 'private'
        self.entries = [(LIBRARY, b'library', stat.S_IFREG | 0o755, 1),
                        (LICENSE, b'BSD license', stat.S_IFREG | 0o644, 1)]

    def extract(self, entries=None, **options):
        self.archive.write_bytes(rpm(cpio(self.entries if entries is None else entries)))
        return native_archive.extract_rpm_files(
            self.archive, self.destination, (LIBRARY, LICENSE), **options)

    def test_extracts_only_exact_regular_allowlist_and_ignores_safe_links(self):
        entries = self.entries + [
            ('usr/lib64/libcudd-3.0.0.so.0', b'libcudd-3.0.0.so.0.0.0', stat.S_IFLNK | 0o777, 1),
            ('usr/bin/package-hook', b'never executed', stat.S_IFREG | 0o755, 1)]
        files = self.extract(entries)
        self.assertEqual(files[LIBRARY].read_bytes(), b'library')
        self.assertEqual(files[LICENSE].read_bytes(), b'BSD license')
        self.assertFalse((self.destination / 'usr/bin/package-hook').exists())
        self.assertFalse((self.destination / 'usr/lib64/libcudd-3.0.0.so.0').exists())
        self.assertEqual(files[LIBRARY].stat().st_mode & 0o111, 0)

    def test_rejects_absolute_traversal_unsafe_links_specials_and_duplicates(self):
        malicious = [
            ('../outside', b'', stat.S_IFREG, 1),
            ('/absolute', b'', stat.S_IFREG, 1),
            ('bad\0name', b'', stat.S_IFREG, 1),
            ('usr/escape', b'../../outside', stat.S_IFLNK, 1),
            ('usr/escape', b'/outside', stat.S_IFLNK, 1),
            ('usr/device', b'', stat.S_IFCHR, 1),
            ('./' + LIBRARY, b'duplicate', stat.S_IFREG, 1),
        ]
        for entry in malicious:
            with self.subTest(entry=entry), self.assertRaises(RuntimeError):
                self.extract(self.entries + [entry])
            self.assertFalse(self.destination.exists())

    def test_selected_hardlinks_symlinks_and_directories_are_rejected(self):
        for mode, links, data in ((stat.S_IFREG, 2, b'hardlink'),
                                  (stat.S_IFLNK, 1, b'other-file'),
                                  (stat.S_IFDIR, 1, b'')):
            with self.subTest(mode=mode), self.assertRaises(RuntimeError):
                self.extract([(LIBRARY, data, mode, links), self.entries[1]])
            self.assertFalse(self.destination.exists())

    def test_missing_files_trailer_and_truncated_file_data_are_rejected(self):
        payloads = [cpio(self.entries[:1]), cpio(self.entries, trailer=False),
                    cpio(self.entries)[:130], b'070701' + b'z' * 104,
                    b'070701' + b'0' * 104]
        for payload in payloads:
            with self.subTest(payload=payload[:12]):
                self.archive.write_bytes(rpm(payload))
                with self.assertRaises(RuntimeError):
                    native_archive.extract_rpm_files(
                        self.archive, self.destination, (LIBRARY, LICENSE))
                self.assertFalse(self.destination.exists())

    def test_invalid_rpm_header_and_xz_payload_are_rejected(self):
        valid = rpm(cpio(self.entries))
        broken = [b'not RPM', valid[:100], valid[:96] + b'badhead!' + valid[104:],
                  valid[:128] + b'not XZ', valid[:-5], valid + b'garbage',
                  valid[:104] + struct.pack('>II', 99999999, 0) + valid[112:]]
        for data in broken:
            with self.subTest(size=len(data)):
                self.archive.write_bytes(data)
                with self.assertRaises(RuntimeError):
                    native_archive.extract_rpm_files(
                        self.archive, self.destination, (LIBRARY, LICENSE))

    def test_compressed_and_expanded_size_limits_are_enforced(self):
        with self.assertRaisesRegex(RuntimeError, 'archive exceeds'):
            self.extract(max_archive_bytes=1)
        with self.assertRaisesRegex(RuntimeError, 'oversized'):
            self.extract(max_payload_bytes=10)
        with mock.patch.object(native_archive.lzma, 'LZMADecompressor',
                               side_effect=lzma.LZMAError('Memory usage limit exceeded')) as decoder:
            with self.assertRaisesRegex(RuntimeError, 'excessive-memory'):
                self.extract()
            self.assertEqual(decoder.call_args.kwargs['memlimit'], 64 * 1024 * 1024)

    def test_existing_destination_symlink_is_not_followed(self):
        outside = self.root / 'outside'
        outside.mkdir()
        self.destination.mkdir()
        (self.destination / 'usr').symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, 'escapes'):
            self.extract()
        self.assertEqual(list(outside.iterdir()), [])

    def test_bounded_download_checks_hash_headers_stream_size_and_no_overwrite(self):
        content = b'official pinned bytes'
        expected = hashlib.sha256(content).hexdigest()
        for label, headers, limit, digest, success in (
                ('valid', {}, 100, expected, True),
                ('hash', {}, 100, '0' * 64, False),
                ('header', {'Content-Length': '101'}, 100, expected, False),
                ('bad-header', {'Content-Length': '-1'}, 100, expected, False),
                ('stream', {}, 4, expected, False)):
            with self.subTest(label=label):
                response = io.BytesIO(content)
                response.headers = headers
                target = self.root / label
                with mock.patch.object(native_archive.urllib.request, 'urlopen', return_value=response):
                    if success:
                        native_archive.download_pinned('https://official/package', target,
                                                       digest, max_bytes=limit)
                        self.assertEqual(target.read_bytes(), content)
                    else:
                        with self.assertRaises(RuntimeError):
                            native_archive.download_pinned('https://official/package', target,
                                                           digest, max_bytes=limit)
        target = self.root / 'existing'
        target.write_bytes(b'preserve')
        response = io.BytesIO(content); response.headers = {}
        with mock.patch.object(native_archive.urllib.request, 'urlopen', return_value=response):
            with self.assertRaises(FileExistsError):
                native_archive.download_pinned('https://official/package', target, expected, max_bytes=100)
        self.assertEqual(target.read_bytes(), b'preserve')


if __name__ == '__main__':
    unittest.main()
