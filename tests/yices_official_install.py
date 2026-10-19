"""Pinned official Yices installation never modifies operating-system packages."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest
from unittest import mock

from stlmc.cli import installer


class OfficialYicesInstallationTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.active = self.root / 'yices' / 'active.json'
        self.active.parent.mkdir()
        self.previous = '{"library": "/previous/user/libyices.so"}'
        self.active.write_text(self.previous)
        self.archive = self.root / 'release.tar.gz'
        with tarfile.open(self.archive, 'w:gz') as output:
            self.member(output, 'yices-2.7.0/lib/libyices.so.2.7.0', b'library')
        digest = hashlib.sha256(self.archive.read_bytes()).hexdigest()
        for patch in (
            mock.patch.object(installer, 'solver_data_dir', return_value=self.root),
            mock.patch.object(installer.sys, 'platform', 'linux'),
            mock.patch.object(installer.platform, 'machine', return_value='x86_64'),
            mock.patch.object(installer, 'YICES_BINARY_ARCHIVES',
                              {('linux', 'x86_64'): ('release.tar.gz', digest)}),
            mock.patch.object(installer, 'download_pinned',
                              side_effect=self.download),
            mock.patch.object(installer, '_install_yices_dependencies', return_value=[]),
            mock.patch.object(installer.platform, 'libc_ver', return_value=('glibc', '2.29')),
        ):
            patch.start()
            self.addCleanup(patch.stop)

    def download(self, url, target, expected, **kwargs):
        if hashlib.sha256(self.archive.read_bytes()).hexdigest() != expected:
            raise RuntimeError('Native package SHA256 mismatch')
        shutil.copyfile(self.archive, target)

    @staticmethod
    def member(archive, name, data):
        entry = tarfile.TarInfo(name)
        entry.size = len(data)
        archive.addfile(entry, io.BytesIO(data))

    def test_only_verified_private_library_is_atomically_activated(self):
        with mock.patch.object(installer, '_probe_library', return_value={
                'version': '2.7.0', 'mcsat': True, 'thread_safe': False}) as probe:
            result = installer.install_official_yices()
        self.assertEqual(json.loads(self.active.read_text()), result)
        self.assertEqual(result['installation'], 'official-binary')
        self.assertTrue(Path(result['library']).is_relative_to(self.root / 'yices' / 'releases'))
        self.assertTrue(Path(result['library']).is_file())
        probe.assert_called_once_with(Path(result['library']))

    def test_bad_hash_never_probes_or_changes_activation(self):
        with mock.patch.object(installer, 'YICES_BINARY_ARCHIVES',
                               {('linux', 'x86_64'): ('release.tar.gz', '0' * 64)}), \
                mock.patch.object(installer, '_probe_library') as probe:
            with self.assertRaisesRegex(RuntimeError, 'SHA256 mismatch'):
                installer.install_official_yices()
        probe.assert_not_called()
        self.assertEqual(self.active.read_text(), self.previous)

    def test_wrong_version_missing_mcsat_or_loader_failure_preserves_previous(self):
        for capabilities in ({'version': '2.6.5', 'mcsat': True},
                             {'version': '2.7.0', 'mcsat': False}, OSError('missing CUDD')):
            with self.subTest(capabilities=capabilities):
                options = ({'side_effect': capabilities} if isinstance(capabilities, Exception)
                           else {'return_value': capabilities})
                with mock.patch.object(installer, '_probe_library', **options):
                    with self.assertRaisesRegex(RuntimeError, '--build'):
                        installer.install_official_yices()
                self.assertEqual(self.active.read_text(), self.previous)

    def test_unsupported_platform_does_not_download(self):
        with mock.patch.object(installer.platform, 'machine', return_value='riscv64'), \
                mock.patch.object(installer, 'download_pinned') as download:
            with self.assertRaisesRegex(RuntimeError, '--build'):
                installer.install_official_yices()
        download.assert_not_called()

    def test_old_macos_is_rejected_before_download(self):
        for machine, release in (('x86_64', '11.7'), ('arm64', '14.7'), ('arm64', '')):
            with self.subTest(machine=machine, release=release), \
                    mock.patch.object(installer.sys, 'platform', 'darwin'), \
                    mock.patch.object(installer.platform, 'machine', return_value=machine), \
                    mock.patch.object(installer.platform, 'mac_ver', return_value=(release, (), '')), \
                    mock.patch.object(installer, 'YICES_BINARY_ARCHIVES',
                                      {('darwin', machine): ('release.tar.gz', 'unused')}), \
                    mock.patch.object(installer, 'download_pinned') as download:
                with self.assertRaisesRegex(RuntimeError, '--build'):
                    installer.install_official_yices()
                download.assert_not_called()

    def test_linux_musl_old_or_unknown_glibc_is_rejected_before_download(self):
        for name, version in (('musl', '1.2.5'), ('glibc', '2.28'), ('glibc', 'unknown'), ('', '')):
            with self.subTest(name=name, version=version), \
                    mock.patch.object(installer.platform, 'libc_ver', return_value=(name, version)), \
                    mock.patch.object(installer.os, 'confstr', return_value=None), \
                    mock.patch.object(installer, 'download_pinned') as download:
                with self.assertRaisesRegex(RuntimeError, 'glibc 2.29'):
                    installer.install_official_yices()
                download.assert_not_called()
                self.assertEqual(self.active.read_text(), self.previous)

    def test_dependency_failure_never_activates_and_verified_dependencies_are_probed(self):
        with mock.patch.object(installer, '_install_yices_dependencies',
                               side_effect=RuntimeError('CUDD SHA256 mismatch')), \
                mock.patch.object(installer, '_probe_library') as probe:
            with self.assertRaisesRegex(RuntimeError, 'CUDD SHA256'):
                installer.install_official_yices()
            probe.assert_not_called()
            self.assertEqual(self.active.read_text(), self.previous)
        dependency = dict(library='/managed/cudd.so', sha256='f' * 64, version='3.0.0',
                          source=installer.CUDD_RPM_URL, package_sha256=installer.CUDD_RPM_SHA256)
        with mock.patch.object(installer, '_install_yices_dependencies', return_value=[dependency]), \
                mock.patch.object(installer, '_probe_library', return_value={
                    'version': '2.7.0', 'mcsat': True, 'thread_safe': False}) as probe:
            result = installer.install_official_yices()
        self.assertEqual(result['dependencies'], [dependency])
        probe.assert_called_once_with(Path(result['library']), [dependency])

    def test_reinstall_uses_fresh_directory_and_keeps_previous_files(self):
        with mock.patch.object(installer, '_probe_library', return_value={
                'version': '2.7.0', 'mcsat': True, 'thread_safe': False}):
            first = installer.install_official_yices()
            second = installer.install_official_yices()
        self.assertNotEqual(first['library'], second['library'])
        self.assertTrue(Path(first['library']).is_file())

    def test_extract_rejects_traversal_links_and_special_files(self):
        for name, kind in (('../escaped', tarfile.REGTYPE),
                           ('/absolute', tarfile.REGTYPE),
                           ('yices/link', tarfile.SYMTYPE),
                           ('yices/hard', tarfile.LNKTYPE),
                           ('yices/device', tarfile.CHRTYPE)):
            with self.subTest(name=name), tarfile.open(self.archive, 'w:gz') as output:
                entry = tarfile.TarInfo(name)
                entry.type = kind
                entry.linkname = '../../escaped'
                output.addfile(entry)
            destination = self.root / 'extract'
            destination.mkdir(exist_ok=True)
            with self.assertRaisesRegex(RuntimeError, 'Unsafe'):
                installer._extract_source(self.archive, destination)
        self.assertFalse((self.root / 'escaped').exists())

    def test_tar_expansion_limit_is_checked_before_skipping_declared_huge_file(self):
        with tarfile.open(self.archive, 'w:gz') as output:
            entry = tarfile.TarInfo('yices-2.7.0/huge')
            entry.size = 1024 * 1024 * 1024
            output.addfile(entry)
        destination = self.root / 'extract'
        destination.mkdir()
        with self.assertRaisesRegex(RuntimeError, 'extraction size'):
            installer._extract_source(self.archive, destination, max_bytes=128 * 1024 * 1024)
        self.assertEqual(list(destination.iterdir()), [])


if __name__ == '__main__':
    unittest.main()
