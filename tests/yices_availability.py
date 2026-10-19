"""Managed official Yices binaries share the native-build discovery contract."""

import ctypes.util
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))

from stlmc.exceptions import SolverUnavailableError
from stlmc.solver import availability


class ManagedYicesDiscoveryTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.library = self.root / 'yices/official-2.7.0/lib/libyices.so.2.7'
        self.library.parent.mkdir(parents=True)
        self.library.touch()
        self.environment = mock.patch.dict(os.environ, {'XDG_DATA_HOME': str(self.root)})
        self.environment.start()
        self.addCleanup(self.environment.stop)
        os.environ.pop('STLMC_YICES_LIBRARY', None)
        self.platform = mock.patch.object(availability.sys, 'platform', 'linux')
        self.platform.start()
        self.addCleanup(self.platform.stop)
        self.modules = mock.patch.dict(sys.modules)
        self.modules.start()
        self.addCleanup(self.modules.stop)
        self.handles = mock.patch.object(availability, '_yices_dependency_handles', {})
        self.handles.start()
        self.addCleanup(self.handles.stop)
        self.selection = mock.patch.object(availability, '_yices_managed_selection', None)
        self.selection.start()
        self.addCleanup(self.selection.stop)
        for name in ('yices', 'yices_api', 'cvc5'):
            sys.modules.pop(name, None)

    def activate(self, library=None, dependencies=None):
        manifest = availability.solver_data_dir() / 'yices/active.json'
        manifest.parent.mkdir(parents=True, exist_ok=True)
        manifest.write_text(json.dumps({
            'library': str(library or self.library), 'version': '2.7.0',
            'source': 'official-release', 'thread_safe': True,
            'dependencies': dependencies or [],
        }))

    def dependency(self):
        path = self.root / 'managed/libcudd.so'
        path.parent.mkdir(exist_ok=True)
        path.write_bytes(b'fake native dependency for loader contract tests')
        return {'library': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'version': '3.0.0', 'source': 'https://download.opensuse.org/example.rpm',
                'package_sha256': 'a' * 64}

    def test_official_manifest_precedes_system_library(self):
        self.activate()
        with mock.patch('ctypes.util.find_library', return_value='/system/libyices.so.2.6.5'):
            self.assertEqual(availability.selected_yices_library(), str(self.library))

    def test_explicit_override_precedes_official_manifest(self):
        self.activate()
        alternate = self.root / 'custom.so'
        alternate.touch()
        os.environ['STLMC_YICES_LIBRARY'] = str(alternate)
        self.assertEqual(availability.selected_yices_library(), str(alternate))

    def test_missing_official_library_never_falls_back_to_old_system(self):
        self.activate(self.root / 'missing.so')
        with self.assertRaisesRegex(SolverUnavailableError, 'not found.*stlmc-installer'):
            availability.load_yices_binding()

    def test_failed_import_restores_global_library_discovery(self):
        self.activate()
        with mock.patch('ctypes.util.find_library', return_value='system') as original:
            with mock.patch('importlib.import_module', side_effect=ImportError('binding missing')):
                with self.assertRaises(ImportError):
                    availability.load_yices_binding()
            self.assertIs(ctypes.util.find_library, original)

    def test_cached_low_level_old_library_cannot_bypass_managed_selection(self):
        self.activate()
        sys.modules['yices_api'] = SimpleNamespace(libyices=SimpleNamespace(_name='/system/libyices.so.2.6.5'))
        with mock.patch('importlib.import_module') as load:
            with self.assertRaisesRegex(SolverUnavailableError, 'restart the process'):
                availability.load_yices_binding()
            load.assert_not_called()

    def test_cached_same_native_library_allows_high_level_binding_import(self):
        self.activate()
        sys.modules['yices_api'] = SimpleNamespace(libyices=SimpleNamespace(_name=str(self.library)))
        binding = SimpleNamespace()
        with mock.patch('importlib.import_module', return_value=binding):
            self.assertIs(availability.load_yices_binding(), binding)

    def test_live_binding_is_reused_when_managed_library_matches(self):
        self.activate()
        binding = SimpleNamespace()
        sys.modules['yices'] = binding
        sys.modules['yices_api'] = SimpleNamespace(libyices=SimpleNamespace(_name=str(self.library)))
        with mock.patch('importlib.import_module') as load:
            self.assertIs(availability.load_yices_binding(), binding)
            load.assert_not_called()

    def test_manifest_flags_do_not_override_actual_native_capabilities(self):
        self.activate()
        binding = SimpleNamespace(Yices=SimpleNamespace(is_thread_safe=lambda: False))
        with mock.patch('importlib.import_module', return_value=binding):
            # Discovery selects the file; execution guards must query Yices.
            self.assertFalse(availability.load_yices_binding().Yices.is_thread_safe())

    def test_dependencies_are_preloaded_before_import_and_handles_are_retained(self):
        dependency = self.dependency()
        self.activate(dependencies=[dependency])
        handle = SimpleNamespace()
        binding = SimpleNamespace()
        def imported(name):
            self.assertEqual(name, 'yices')
            self.assertEqual(list(availability._yices_dependency_handles.values()), [handle])
            return binding
        with mock.patch('ctypes.CDLL', return_value=handle) as cdll, \
                mock.patch('importlib.import_module', side_effect=imported):
            self.assertIs(availability.load_yices_binding(), binding)
            cdll.assert_called_once_with(dependency['library'], mode=ctypes.RTLD_GLOBAL)

    def test_explicit_library_does_not_inherit_managed_dependencies(self):
        self.activate(dependencies=[{'library': '/missing/dependency.so'}])
        os.environ['STLMC_YICES_LIBRARY'] = str(self.library)
        with mock.patch('ctypes.CDLL') as cdll, mock.patch('importlib.import_module'):
            availability.load_yices_binding()
            cdll.assert_not_called()

    def test_corrupt_or_missing_dependency_does_not_fall_back_to_system(self):
        for failure in ('changed-content', 'missing-file'):
            with self.subTest(failure=failure):
                dependency = self.dependency()
                self.activate(dependencies=[dependency])
                path = Path(dependency['library'])
                if failure == 'missing-file':
                    path.unlink()
                else:
                    path.write_bytes(b'changed after installation')
                with mock.patch('ctypes.CDLL') as cdll, mock.patch('importlib.import_module') as imported:
                    with self.assertRaisesRegex(SolverUnavailableError, 'invalid Yices dependency'):
                        availability.load_yices_binding()
                    cdll.assert_not_called()
                    imported.assert_not_called()

    def test_dependency_metadata_requires_absolute_path_hash_and_provenance(self):
        for key, invalid in [('library', 'relative.so'), ('sha256', 'bad'),
                             ('package_sha256', 'bad'), ('version', ''),
                             ('source', 'http://example.com/not-https.rpm')]:
            with self.subTest(key=key):
                dependency = self.dependency()
                dependency[key] = invalid
                self.activate(dependencies=[dependency])
                with self.assertRaisesRegex(SolverUnavailableError, 'invalid Yices dependency'):
                    availability.selected_yices_library()

    def test_native_dependency_load_failure_is_actionable(self):
        self.activate(dependencies=[self.dependency()])
        with mock.patch('ctypes.CDLL', side_effect=OSError('incompatible GLIBC')), \
                mock.patch('importlib.import_module') as imported:
            with self.assertRaisesRegex(SolverUnavailableError, 'could not load managed.*stlmc-installer'):
                availability.load_yices_binding()
            imported.assert_not_called()

    def test_live_dependency_selection_changes_require_restart(self):
        dependency = self.dependency()
        self.activate(dependencies=[dependency])
        sys.modules['yices'] = SimpleNamespace()
        sys.modules['yices_api'] = SimpleNamespace(libyices=SimpleNamespace(_name=str(self.library)))
        availability._yices_managed_selection = (str(self.library), ())
        with self.assertRaisesRegex(SolverUnavailableError, 'dependencies changed.*restart'):
            availability.load_yices_binding()

    def test_loaded_binding_reuse_does_not_preload_dependencies_twice(self):
        dependency = self.dependency()
        self.activate(dependencies=[dependency])
        binding = SimpleNamespace()
        with mock.patch('ctypes.CDLL') as cdll, mock.patch('importlib.import_module', return_value=binding):
            availability.load_yices_binding()
            sys.modules['yices'] = binding
            sys.modules['yices_api'] = SimpleNamespace(libyices=SimpleNamespace(_name=str(self.library)))
            self.assertIs(availability.load_yices_binding(), binding)
            cdll.assert_called_once()

    def test_removing_dependencies_from_a_live_selection_requires_restart(self):
        dependency = self.dependency()
        self.activate(dependencies=[dependency])
        binding = SimpleNamespace()
        with mock.patch('ctypes.CDLL'), mock.patch('importlib.import_module', return_value=binding):
            availability.load_yices_binding()
        sys.modules['yices'] = binding
        sys.modules['yices_api'] = SimpleNamespace(libyices=SimpleNamespace(_name=str(self.library)))
        for explicit in (False, True):
            with self.subTest(explicit=explicit):
                if explicit:
                    os.environ['STLMC_YICES_LIBRARY'] = str(self.library)
                else:
                    self.activate()
                with self.assertRaisesRegex(SolverUnavailableError, 'dependencies changed.*restart'):
                    availability.load_yices_binding()

    def test_failed_import_cannot_switch_already_preloaded_dependencies(self):
        dependency = self.dependency()
        self.activate(dependencies=[dependency])
        with mock.patch('ctypes.CDLL'), mock.patch('importlib.import_module', side_effect=ImportError('missing binding')):
            with self.assertRaises(ImportError):
                availability.load_yices_binding()
        self.activate()
        with mock.patch('importlib.import_module') as imported:
            with self.assertRaisesRegex(SolverUnavailableError, 'dependencies are already loaded.*restart'):
                availability.load_yices_binding()
            imported.assert_not_called()


if __name__ == '__main__':
    unittest.main()
