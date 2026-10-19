"""CI executable setup retains managed native dependency search paths."""
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('ci_solvers',
    Path(__file__).resolve().parents[1] / 'tools/setup_ci_solvers.py')
TOOL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOL)


class CiSolverEnvironmentTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.library = self.root / 'lib/libyices.so'
        self.library.parent.mkdir()
        self.library.touch()
        self.executable = self.root / 'bin/yices-smt2'
        self.executable.parent.mkdir()
        self.executable.touch(mode=0o755)
        self.dependency = self.root / 'dependencies/cudd/libcudd.so'
        self.dependency.parent.mkdir(parents=True)
        self.dependency.touch()
        self.manifest = self.root / 'active.json'
        self.manifest.write_text(json.dumps({'prefix': str(self.root),
            'library': str(self.library),
            'dependencies': [{'library': str(self.dependency)}]}))

    def environment(self, platform='linux'):
        return TOOL.yices_environment(self.manifest, self.library,
            {'PATH': '/existing/bin', 'LD_LIBRARY_PATH': '/existing/lib',
             'DYLD_LIBRARY_PATH': '/opt/homebrew/lib'}, platform)

    def test_linux_preserves_existing_paths_and_adds_dependencies(self):
        values = self.environment()
        self.assertEqual(values['PATH'].split(os.pathsep)[0], str(self.executable.parent))
        self.assertEqual(values['LD_LIBRARY_PATH'].split(os.pathsep),
            [str(self.library.parent), str(self.dependency.parent), '/existing/lib'])

    def test_mac_preserves_homebrew_dependency_directory(self):
        values = self.environment('darwin')
        self.assertTrue(values['DYLD_LIBRARY_PATH'].endswith('/opt/homebrew/lib'))
        self.assertNotIn('LD_LIBRARY_PATH', values)

    def test_missing_cli_is_an_error(self):
        self.executable.unlink()
        with self.assertRaisesRegex(RuntimeError, 'executable'):
            self.environment()

    def test_explicit_library_mismatch_is_an_error(self):
        other = self.root / 'other.so'
        other.touch()
        with self.assertRaisesRegex(RuntimeError, 'managed'):
            TOOL.yices_environment(self.manifest, other, {}, 'linux')


if __name__ == '__main__':
    unittest.main()
