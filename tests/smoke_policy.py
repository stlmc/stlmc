"""Known-defect release observations must never weaken default smoke checks."""
import contextlib
import io
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

import smoke_solvers as smoke


class SmokePolicyTest(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.folder = Path(directory.name)
        self.input = self.folder / smoke.KNOWN_DREAL_CASE
        for suffix in ('', '.args', '.expected'):
            source = smoke.TEST_ROOT / 'dreal' / (smoke.KNOWN_DREAL_CASE + suffix)
            shutil.copyfile(source, self.folder / source.name)

    def result(self, output, code=0, stderr=''):
        return subprocess.CompletedProcess([], code, output, stderr)

    def version(self, token='3.16.06.02'):
        return self.result('dReal v{} (commit d6645637507b)\n'.format(token))

    def invoke(self, responses, allow=True):
        output = io.StringIO()
        with mock.patch.object(smoke.subprocess, 'run', side_effect=responses) as execute, \
                contextlib.redirect_stdout(output):
            counts = smoke.run_solver('dReal', '/solver/dReal', self.folder,
                                      allow_known_dreal_bugs=allow)
        return counts, output.getvalue(), execute

    def test_default_remains_strict_without_even_probing_version(self):
        with mock.patch.object(smoke.subprocess, 'run', return_value=self.result(smoke.KNOWN_DREAL_OUTPUT)) as execute:
            with self.assertRaises(AssertionError):
                smoke.run_solver('dReal', '/solver/dReal', self.folder)
        self.assertEqual(execute.call_count, 1)

    def test_only_exact_official_known_output_is_xfail(self):
        counts, output, execute = self.invoke([self.version(), self.result(smoke.KNOWN_DREAL_OUTPUT)])
        self.assertEqual(counts, {'PASS': 0, 'XFAIL': 1, 'XPASS': 0})
        self.assertIn('[XFAIL]', output)
        self.assertIn('not a correctness pass', output)
        self.assertEqual(execute.call_args_list[0].args[0], ['/solver/dReal', '--version'])

    def test_correct_result_is_successful_xpass(self):
        counts, output, _ = self.invoke([self.version(), self.result('unsat\n')])
        self.assertEqual(counts, {'PASS': 0, 'XFAIL': 0, 'XPASS': 1})
        self.assertIn('[XPASS]', output)

    def test_other_version_and_version_suffix_cannot_xfail(self):
        for version in ('3.16.12', '3.16.06.02-custom', '3.16.06.020'):
            with self.subTest(version=version), self.assertRaises(AssertionError):
                self.invoke([self.version(version), self.result(smoke.KNOWN_DREAL_OUTPUT)])

    def test_fixture_arguments_and_expected_hashes_are_all_required(self):
        for suffix in ('', '.args', '.expected'):
            path = self.folder / (smoke.KNOWN_DREAL_CASE + suffix)
            original = path.read_bytes()
            path.write_bytes(original + b'\n')
            with self.subTest(suffix=suffix), \
                    mock.patch.object(smoke.subprocess, 'run') as execute, \
                    self.assertRaisesRegex(RuntimeError, 'fingerprint changed'):
                smoke.run_solver('dReal', '/solver/dReal', self.folder,
                                 allow_known_dreal_bugs=True)
            execute.assert_not_called()
            path.write_bytes(original)

    def test_unknown_conflicting_status_and_extra_output_remain_failures(self):
        for output in ('unknown\n', 'sat\n', smoke.KNOWN_DREAL_OUTPUT+'unsat\n',
                       'diagnostic\n'+smoke.KNOWN_DREAL_OUTPUT):
            with self.subTest(output=output), self.assertRaises(AssertionError):
                self.invoke([self.version(), self.result(output)])

    def test_nonzero_exit_and_stderr_cannot_be_xfail(self):
        for result in (self.result(smoke.KNOWN_DREAL_OUTPUT, code=-11),
                       self.result(smoke.KNOWN_DREAL_OUTPUT, stderr='ODE error'),
                       self.result('unsat\n', stderr='ODE error')):
            with self.subTest(result=result), self.assertRaises(RuntimeError):
                self.invoke([self.version(), result])

    def test_version_probe_errors_and_timeouts_remain_failures(self):
        for version in (self.result('', code=1), self.result('', stderr='loader error')):
            with self.subTest(version=version), self.assertRaises(RuntimeError):
                self.invoke([version])
        for responses in ([subprocess.TimeoutExpired('dReal', 5)],
                          [self.version(), subprocess.TimeoutExpired('dReal', 30)]):
            with self.subTest(responses=responses), self.assertRaises(subprocess.TimeoutExpired):
                self.invoke(responses)

    def test_other_fixture_is_not_covered_even_with_identical_bytes(self):
        for suffix in ('', '.args', '.expected'):
            (self.folder / (smoke.KNOWN_DREAL_CASE+suffix)).rename(self.folder / ('other.smt2'+suffix))
        with mock.patch.object(smoke.subprocess, 'run', return_value=self.result(smoke.KNOWN_DREAL_OUTPUT)) as execute:
            with self.assertRaises(AssertionError):
                smoke.run_solver('dReal', '/solver/dReal', self.folder,
                                 allow_known_dreal_bugs=True)
        self.assertEqual(execute.call_count, 1)

    def test_positive_and_interior_peak_inputs_never_receive_an_exception(self):
        for name in ('zero-derivative-parameter-sat.smt2', 'interior-peak.smt2'):
            with tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                for suffix in ('', '.args', '.expected'):
                    source = smoke.TEST_ROOT / 'dreal' / (name+suffix)
                    shutil.copyfile(source, folder/source.name)
                # Deliberately return the opposite result, with the flag set.
                actual = 'unsat\n' if 'parameter-sat' in name else smoke.KNOWN_DREAL_OUTPUT
                with self.subTest(name=name), \
                        mock.patch.object(smoke.subprocess, 'run', return_value=self.result(actual)) as execute, \
                        self.assertRaises(AssertionError):
                    smoke.run_solver('dReal', '/solver/dReal', folder,
                                     allow_known_dreal_bugs=True)
                self.assertEqual(execute.call_count, 1)

    def test_summary_separates_known_defects_from_passes(self):
        output = io.StringIO()
        with mock.patch.object(smoke, 'find_executable', return_value='/solver/native'), \
                mock.patch.object(smoke, 'run_solver', side_effect=[
                    {'PASS': 2, 'XPASS': 0, 'XFAIL': 0},
                    {'PASS': 1, 'XPASS': 0, 'XFAIL': 0},
                    {'PASS': 4, 'XPASS': 0, 'XFAIL': 1}]) as run, \
                contextlib.redirect_stdout(output):
            counts = smoke.main(['--allow-known-dreal-bugs'])
        self.assertEqual(counts, {'PASS': 7, 'XPASS': 0, 'XFAIL': 1})
        self.assertIn('7 PASS, 0 XPASS, 1 known-defect XFAIL', output.getvalue())
        self.assertTrue(all(c.kwargs['allow_known_dreal_bugs'] for c in run.call_args_list))


if __name__ == '__main__':
    unittest.main()
