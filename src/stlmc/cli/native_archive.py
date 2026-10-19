"""Bounded native-package downloads and selective, non-installing RPM reads.

No package scripts, external extractors, permissions, links, or package-manager
operations are executed. Callers must pin the downloaded bytes before decoding.
"""
import hashlib
import lzma
from pathlib import Path, PurePosixPath
import stat
import struct
import urllib.request


def download_pinned(url, target, expected_sha256, *, max_bytes):
    digest = hashlib.sha256()
    size = 0
    with urllib.request.urlopen(url, timeout=30) as response, Path(target).open('xb') as output:
        length = response.headers.get('Content-Length')
        if length is not None and (not length.isdecimal() or int(length) > max_bytes):
            raise RuntimeError('Native package Content-Length exceeds the permitted download size')
        while True:
            chunk = response.read(min(1024 * 1024, max_bytes - size + 1))
            if not chunk:
                break
            size += len(chunk)
            if size > max_bytes:
                raise RuntimeError('Native package exceeds the permitted download size')
            output.write(chunk)
            digest.update(chunk)
    if digest.hexdigest() != expected_sha256:
        raise RuntimeError('Native package SHA256 mismatch: ' + url)


def _rpm_payload(data, max_payload_bytes):
    if len(data) < 96 or data[:4] != b'\xed\xab\xee\xdb' or data[4] != 3:
        raise RuntimeError('Invalid RPM lead')
    offset = 96
    for signature in (True, False):
        if data[offset:offset + 8] != b'\x8e\xad\xe8\x01\0\0\0\0' or offset + 16 > len(data):
            raise RuntimeError('Invalid RPM header')
        count, size = struct.unpack('>II', data[offset + 8:offset + 16])
        if count > 4096 or size > 2 * 1024 * 1024:
            raise RuntimeError('RPM header exceeds permitted size')
        offset += 16 + 16 * count + size
        if offset > len(data):
            raise RuntimeError('Truncated RPM header')
        if signature:
            offset = (offset + 7) // 8 * 8
    if not data[offset:].startswith(b'\xfd7zXZ\0'):
        raise RuntimeError('Only XZ-compressed RPM payloads are supported')
    try:
        decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=64 * 1024 * 1024)
        payload = decoder.decompress(data[offset:], max_length=max_payload_bytes + 1)
    except lzma.LZMAError as error:
        raise RuntimeError('Invalid or excessive-memory RPM XZ payload') from error
    if len(payload) > max_payload_bytes or not decoder.eof or decoder.unused_data:
        raise RuntimeError('Truncated or oversized RPM payload')
    return payload


def _safe_path(name):
    path = PurePosixPath(name)
    if not name or '\0' in name or path.is_absolute() or '..' in path.parts:
        raise RuntimeError('Unsafe RPM archive path: ' + name)
    return path


def extract_rpm_files(archive, destination, expected_files, *,
                      max_archive_bytes=2 * 1024 * 1024,
                      max_payload_bytes=16 * 1024 * 1024):
    """Read a bounded newc payload, saving exactly the allowlisted regular files.

    Safe relative symlinks are ignored, never created or followed. Special
    entries, traversal, duplicate paths, and selected hardlinks are rejected.
    All archive metadata is checked before any selected file is written.
    """
    if Path(archive).stat().st_size > max_archive_bytes:
        raise RuntimeError('RPM archive exceeds permitted size')
    data = Path(archive).read_bytes()
    if len(data) > max_archive_bytes:
        raise RuntimeError('RPM archive exceeds permitted size')
    payload = _rpm_payload(data, max_payload_bytes)
    selected, seen = {}, set()
    offset = 0
    trailer = False
    for _ in range(10000):
        header = payload[offset:offset + 110]
        if len(header) != 110 or header[:6] != b'070701':
            raise RuntimeError('Invalid RPM newc header')
        if any(byte not in b'0123456789abcdefABCDEF' for byte in header[6:]):
            raise RuntimeError('Invalid RPM newc numeric field')
        try:
            fields = [int(header[6 + 8 * i:14 + 8 * i], 16) for i in range(13)]
        except ValueError as error:
            raise RuntimeError('Invalid RPM newc numeric field') from error
        mode, links, size, namesize = fields[1], fields[4], fields[6], fields[11]
        if fields[12] != 0:
            raise RuntimeError('Invalid RPM newc checksum field')
        if not 1 <= namesize <= 4096:
            raise RuntimeError('Invalid RPM newc filename length')
        start = offset + 110
        raw_name = payload[start:start + namesize]
        if len(raw_name) != namesize or raw_name[-1:] != b'\0':
            raise RuntimeError('Truncated RPM filename')
        try:
            name = raw_name[:-1].decode('utf-8')
        except UnicodeDecodeError as error:
            raise RuntimeError('Invalid RPM filename encoding') from error
        start = (start + namesize + 3) // 4 * 4
        end = start + size
        if end > len(payload):
            raise RuntimeError('Truncated RPM file')
        content = payload[start:end]
        offset = (end + 3) // 4 * 4
        if name == 'TRAILER!!!':
            if size or any(payload[offset:]):
                raise RuntimeError('Invalid RPM newc trailer')
            trailer = True
            break
        path = _safe_path(name)
        normalized = str(path)
        if normalized in seen:
            raise RuntimeError('Duplicate RPM archive path: ' + name)
        seen.add(normalized)
        if stat.S_ISLNK(mode):
            try:
                _safe_path(content.decode('utf-8'))
            except UnicodeDecodeError as error:
                raise RuntimeError('Invalid RPM symlink target') from error
            if normalized in expected_files:
                raise RuntimeError('Selected RPM file is a symbolic link')
            continue
        if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
            raise RuntimeError('Unsupported RPM special file: ' + name)
        if normalized in expected_files:
            if not stat.S_ISREG(mode) or links != 1:
                raise RuntimeError('Selected RPM file is not a standalone regular file')
            selected[normalized] = content
    if not trailer or set(selected) != set(expected_files):
        raise RuntimeError('RPM payload is missing required regular files or trailer')
    base = Path(destination).resolve()
    for name, content in selected.items():
        target = base.joinpath(*PurePosixPath(name).parts)
        if base not in target.resolve().parents:
            raise RuntimeError('RPM extraction destination escapes its private prefix')
        target.parent.mkdir(parents=True, exist_ok=True)
        if base not in target.resolve().parents:
            raise RuntimeError('RPM extraction destination escapes its private prefix')
        with target.open('xb') as output:
            output.write(content)
    return {name: base.joinpath(*PurePosixPath(name).parts) for name in selected}
