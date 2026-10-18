"""Lightweight version/provenance and public banner contracts."""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / 'src'))

from stlmc import version_info


class VersionInfoTest(unittest.TestCase):
    def test_package_metadata_missing_is_nonfatal(self):
        with mock.patch.object(version_info, 'version', side_effect=version_info.PackageNotFoundError('stlmc')):
            self.assertEqual(version_info.package_version(), 'development')

    def test_banner_has_stable_two_line_layout(self):
        with mock.patch.object(version_info, 'version_line', return_value='v9.8.7 (commit: unknown)'):
            self.assertEqual(version_info.banner(),
                             'STLmc - Signal Temporal Logic Model Checker\nv9.8.7 (commit: unknown)')

    def test_source_commit_without_git_metadata_does_not_call_git(self):
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch.object(version_info.subprocess, 'run') as run:
            self.assertIsNone(version_info._source_commit(Path(directory)))
            run.assert_not_called()

    def test_source_commit_clean_dirty_and_foreign_repository(self):
        for dirty, foreign in ((False, False), (True, False), (False, True)):
            with self.subTest(dirty=dirty, foreign=foreign), tempfile.TemporaryDirectory() as directory:
                root = Path(directory).resolve()
                (root / '.git').mkdir()

                def git(command, **kwargs):
                    self.assertLessEqual(kwargs.get('timeout', 999), 1)
                    self.assertTrue(str(root) in command or Path(kwargs.get('cwd', '.')).resolve() == root)
                    if '--show-toplevel' in command:
                        output = str(root / 'different') if foreign else str(root)
                    elif 'status' in command:
                        output = ' M tracked.py\n' if dirty else ''
                    else:
                        output = '0123456789abcdef0123456789abcdef01234567\n'
                    return subprocess.CompletedProcess(command, 0, output, '')

                with mock.patch.object(version_info.subprocess, 'run', side_effect=git):
                    result = version_info._source_commit(root)
                if foreign:
                    self.assertIsNone(result)
                else:
                    self.assertEqual(result, '0123456789ab' + ('-dirty' if dirty else ''))

    def test_source_git_failures_are_nonfatal(self):
        errors = [FileNotFoundError('git missing'),
                  subprocess.TimeoutExpired(['git'], 1),
                  subprocess.CalledProcessError(128, ['git'])]
        for error in errors:
            with self.subTest(error=type(error).__name__), tempfile.TemporaryDirectory() as directory:
                root=Path(directory)
                (root/'.git').mkdir()
                with mock.patch.object(version_info.subprocess, 'run', side_effect=error):
                    self.assertIsNone(version_info._source_commit(root))

    def test_invalid_git_revision_is_not_displayed(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory).resolve()
            (root/'.git').write_text('gitdir: elsewhere\n')
            outputs=[subprocess.CompletedProcess([],0,str(root),''),
                     subprocess.CompletedProcess([],0,'not-a-hash','')]
            with mock.patch.object(version_info.subprocess,'run',side_effect=outputs):
                self.assertIsNone(version_info._source_commit(root))

    def test_version_line_uses_source_commit(self):
        with mock.patch.object(version_info, 'package_version', return_value='9.8.7'), \
                mock.patch.object(version_info, '_source_commit', return_value='abcdef012345-dirty'):
            self.assertEqual(version_info.version_line(), 'v9.8.7 (commit: abcdef012345-dirty)')

    def test_source_absent_uses_build_commit_or_unknown(self):
        for commit in ('0123456789ab', '0123456789ab-dirty', None, 'not-a-commit'):
            module=types.ModuleType('stlmc._build_info')
            module.COMMIT=commit
            with self.subTest(commit=commit), \
                    mock.patch.object(version_info, 'package_version', return_value='9.8.7'), \
                    mock.patch.object(version_info, '_source_commit', return_value=None), \
                    mock.patch.dict(sys.modules, {'stlmc._build_info': module}):
                expected=commit if commit in ('0123456789ab', '0123456789ab-dirty') else 'unknown'
                self.assertEqual(version_info.version_line(), 'v9.8.7 (commit: '+expected+')')

    def test_help_version_and_execution_header_share_banner_without_heavy_imports(self):
        script = '''
import contextlib, io, sys
from stlmc.version_info import banner, version_line
from stlmc.cli.mc import main
from stlmc.utils.print import BasePrinter
expected=banner()
for argument in ('-h','--version'):
    output=io.StringIO()
    sys.argv=['stlmc',argument]
    with contextlib.redirect_stdout(output):
        try:
            result=main()
            assert result in (0,None), result
        except SystemExit as error:
            assert error.code==0, error.code
    assert expected in output.getvalue(), output.getvalue()
output=io.StringIO()
with contextlib.redirect_stdout(output):
    BasePrinter().run_started('example.model','f1','z3','one-step',False,1,2,
                              'mode changes + STL variable points',3,0.01,'counterexample search')
assert output.getvalue().startswith(expected+'\\n'), output.getvalue()
for name in ('z3','yices','cvc5','numpy','scipy','bokeh','matplotlib','lark'):
    assert name not in sys.modules, name
print('banner consistent; no heavy imports')
'''
        env=dict(os.environ, PYTHONPATH=str(PROJECT_ROOT/'src'))
        with tempfile.TemporaryDirectory() as unrelated_cwd:
            result=subprocess.run([sys.executable,'-c',script], cwd=unrelated_cwd,
                                  env=env, text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)


if __name__ == '__main__':
    unittest.main()
