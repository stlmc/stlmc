"""Feature checks for dReal3; native integration is explicitly opt-in."""

import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
import warnings
from concurrent.futures import ThreadPoolExecutor
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
from stlmc.exceptions import SolverUnavailableError
from stlmc.solver import dreal_runtime as runtime

VERSION = (0, "dReal v3.16.12 (commit test)", "")
SAT = (0, "Solution:\ng_0_t : [-10, 10] = [8, 8]\n"
       "clock_0_t : [0, 10] = [3, 3]\ndelta-sat with delta = 0.000001\n", "")
UNSAT = (0, "unsat\n", "")
OFFICIAL = (0, "dReal v3.16.06.02 (commit official)", "")


class DrealRuntimeTest(unittest.TestCase):
    def test_official_known_failure_is_silent_and_caches_immutable_metadata(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[OFFICIAL, SAT, SAT]) as run, \
                warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            with ThreadPoolExecutor(max_workers=4) as pool:
                results = list(pool.map(lambda _: self.validate(), range(8)))
            results[0]["known_limitations"] = "changed"
            result = self.validate()
        self.assertEqual(run.call_count, 3)
        self.assertEqual(len(caught), 0)
        self.assertFalse(result["zero_derivative_forall"])
        self.assertEqual(result["known_limitations"], runtime.DREAL_KNOWN_LIMITATIONS_WARNING)

    def test_known_limitation_is_allowed_with_warnings_as_errors(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[OFFICIAL, SAT, SAT] * 2) as run, \
                warnings.catch_warnings():
            warnings.simplefilter("error", RuntimeWarning)
            for _ in range(2):
                result = self.validate()
                self.assertFalse(result["zero_derivative_forall"])
                self.assertTrue(runtime._SUCCESS_CACHE)
        self.assertEqual(run.call_count, 3)

    def test_official_exception_requires_valid_unambiguous_negative_model(self):
        negatives = [
            (0, "delta-sat\n", ""),
            (0, SAT[1].replace("[8, 8]", "[7, 7]"), ""),
            (0, SAT[1].replace("[3, 3]", "[0, 0]"), ""),
            (0, SAT[1] + "unknown\n", ""),
            (0, SAT[1] + "delta-sat\n", ""),
            (0, SAT[1].replace("delta-sat with delta = 0.000001", "sat"), ""),
            (0, SAT[1].replace("delta = 0.000001", "delta = invalid"), ""),
            (0, SAT[1], "native error"),
            (-11, SAT[1], ""),
        ]
        for negative in negatives:
            with self.subTest(negative=negative), mock.patch.object(
                    runtime, "_run_bounded", side_effect=[OFFICIAL, SAT, negative]):
                with self.assertRaises(SolverUnavailableError):
                    self.validate()
                self.assertFalse(runtime._SUCCESS_CACHE)

    def test_official_version_suffix_does_not_receive_known_bug_exception(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[
                (0, "dReal v3.16.06.02-custom", ""), SAT, SAT]):
            with self.assertRaises(SolverUnavailableError):
                self.validate()

    def test_direct_adapter_rejects_unsafe_runtime_before_materializing_query(self):
        from stlmc.constraints.constraints import BoolVal
        from stlmc.parser.config_visitor import ConfigVisitor
        from stlmc.solver.dreal import dRealSolver

        config = ConfigVisitor().parse_from_file(str(ROOT / "src/stlmc/default.cfg"))
        solver = dRealSolver(config)
        with mock.patch.object(runtime, "validate_dreal_runtime",
                               side_effect=SolverUnavailableError("unsafe runtime")), \
                mock.patch.object(solver, "_prepare_solver_command") as prepare:
            with self.assertRaisesRegex(SolverUnavailableError, "unsafe runtime"):
                solver.submit(BoolVal("True"))
        prepare.assert_not_called()

    def setUp(self):
        runtime._SUCCESS_CACHE.clear()
        self.directory = tempfile.TemporaryDirectory(prefix="stlmc-runtime-test-")
        self.addCleanup(self.directory.cleanup)
        self.executable = Path(self.directory.name) / "dReal"
        self.executable.write_bytes(b"test executable")
        self.executable.chmod(0o755)

    def validate(self):
        return runtime.validate_dreal_runtime(self.executable)

    def test_positive_and_negative_queries_and_model_are_checked(self):
        seen = []
        def run(command):
            if command[-1] == "--version":
                return VERSION
            text = Path(command[1]).read_text()
            seen.append(text)
            self.assertIn("(= d/dt[g] 0)", text)
            self.assertIn("(= d/dt[clock] 1)", text)
            self.assertIn("Real [3,3]", text)
            self.assertEqual(command[-4:], ["--precision", "0.000001", "--short_sat", "--model"])
            return SAT if "8.5" in text else UNSAT
        with mock.patch.object(runtime, "_run_bounded", side_effect=run):
            result = self.validate()
        self.assertTrue(result["ode_supported"])
        self.assertTrue(result["zero_derivative_forall"])
        self.assertEqual(result["executable"], str(self.executable.resolve()))
        self.assertEqual(len(seen), 2)
        self.assertIn("(< g_0_t 7.5)", seen[1])

    def test_success_is_cached_but_returned_mapping_is_not_shared(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, UNSAT]) as run:
            first = self.validate()
            first["ode_supported"] = False
            second = self.validate()
        self.assertTrue(second["ode_supported"])
        self.assertEqual(run.call_count, 3)

    def test_changed_executable_is_probed_again(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, UNSAT] * 2) as run:
            self.validate()
            self.executable.write_bytes(b"replacement executable with changed size")
            self.validate()
        self.assertEqual(run.call_count, 6)

    def test_same_size_mtime_change_is_probed_again(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, UNSAT] * 2) as run:
            self.validate()
            stat = self.executable.stat()
            os.utime(self.executable, ns=(stat.st_atime_ns, stat.st_mtime_ns + 1000000))
            self.validate()
        self.assertEqual(run.call_count, 6)

    def test_bad_build_is_not_cached(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, SAT] * 2) as run:
            for _ in range(2):
                with self.assertRaisesRegex(SolverUnavailableError, "ignore invariants.*compatible dReal3"):
                    self.validate()
        self.assertEqual(run.call_count, 6)
        self.assertFalse(runtime._SUCCESS_CACHE)

    def test_replacement_inode_with_same_size_and_mtime_is_probed_again(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, UNSAT] * 2) as run:
            self.validate()
            stat = self.executable.stat()
            replacement = self.executable.with_name("replacement")
            replacement.write_bytes(self.executable.read_bytes())
            replacement.chmod(0o755)
            os.utime(replacement, ns=(stat.st_atime_ns, stat.st_mtime_ns))
            replacement.replace(self.executable)
            self.validate()
        self.assertEqual(run.call_count, 6)

    def test_executable_replaced_during_probe_is_not_cached(self):
        def changed(command):
            if command[-1] == "--version":
                self.executable.write_bytes(b"changed during validation")
                return VERSION
            return SAT if Path(command[1]).stem == "positive" else UNSAT
        with mock.patch.object(runtime, "_run_bounded", side_effect=changed):
            with self.assertRaisesRegex(SolverUnavailableError, "changed during validation"):
                self.validate()
        self.assertFalse(runtime._SUCCESS_CACHE)

    def test_dreal4_is_not_an_ode_compatible_runtime(self):
        with mock.patch.object(runtime, "_run_bounded", return_value=(0, "dReal v4.21.06", "")) as run:
            with self.assertRaisesRegex(SolverUnavailableError, "expected a dReal3"):
                self.validate()
        self.assertEqual(run.call_count, 1)

    def test_compatible_major3_is_feature_checked_without_release_pin(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[(0, "dReal v3.99.test", ""), SAT, UNSAT]):
            self.assertIn("3.99", self.validate()["version"])

    def test_positive_sat_requires_actual_integrated_model(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, (0, "delta-sat\n", "")]):
            with self.assertRaisesRegex(SolverUnavailableError, "integrated model"):
                self.validate()

    def test_wrong_clock_value_is_not_native_ode_support(self):
        wrong = (0, SAT[1].replace("[3, 3]", "[0, 0]"), "")
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, wrong]):
            with self.assertRaisesRegex(SolverUnavailableError, "integrated model"):
                self.validate()

    def test_unknown_is_not_unsat(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, (0, "unknown\n", "")]):
            with self.assertRaisesRegex(SolverUnavailableError, "expected UNSAT"):
                self.validate()

    def test_conflicting_statuses_are_not_accepted(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, (0, "delta-sat\nunsat\n", "")]):
            with self.assertRaisesRegex(SolverUnavailableError, "expected UNSAT"):
                self.validate()

    def test_nonzero_exit_is_failure_even_if_stdout_says_unsat(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, (1, "unsat\n", "parse error")]):
            with self.assertRaisesRegex(SolverUnavailableError, "native exit 1: parse error"):
                self.validate()

    def test_timeout_has_an_actionable_error_and_is_not_cached(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=subprocess.TimeoutExpired("dReal", 5)):
            with self.assertRaisesRegex(SolverUnavailableError, "-executable-path"):
                self.validate()
        self.assertFalse(runtime._SUCCESS_CACHE)

    def test_no_installer_known_bad_build_recommendation(self):
        with mock.patch.object(runtime, "_run_bounded", side_effect=[VERSION, SAT, SAT]):
            with self.assertRaises(SolverUnavailableError) as caught:
                self.validate()
        self.assertNotIn("stlmc-installer install", str(caught.exception))

    def test_missing_executable_does_not_launch(self):
        self.executable.unlink()
        with mock.patch.object(runtime, "_run_bounded") as run:
            with self.assertRaises(SolverUnavailableError):
                self.validate()
        run.assert_not_called()

    @unittest.skipUnless(os.name == "posix", "POSIX executable permissions")
    def test_nonexecutable_file_does_not_launch(self):
        self.executable.chmod(0o644)
        with mock.patch.object(runtime, "_run_bounded") as run:
            with self.assertRaises(SolverUnavailableError):
                self.validate()
        run.assert_not_called()

    @unittest.skipUnless(os.name == "posix", "POSIX process-group cleanup")
    def test_timeout_kills_and_reaps_process_group(self):
        process = mock.Mock(pid=123)
        process.communicate.side_effect = [subprocess.TimeoutExpired("dReal", 5), ("", "")]
        with mock.patch.object(runtime.subprocess, "Popen", return_value=process) as launch, \
                mock.patch.object(runtime.os, "killpg") as kill:
            with self.assertRaises(subprocess.TimeoutExpired):
                runtime._run_bounded(["dReal", "--version"])
        kill.assert_called_once_with(123, signal.SIGKILL)
        self.assertEqual(process.communicate.call_count, 2)
        self.assertEqual(process.communicate.call_args_list[0], mock.call(timeout=5))
        self.assertTrue(launch.call_args.kwargs["start_new_session"])


@unittest.skipUnless(os.environ.get("STLMC_TEST_DREAL_RUNTIME_NATIVE") == "1", "opt-in native runtime probes")
class DrealRuntimeNativeTest(unittest.TestCase):
    def test_official_repository_build_silently_reports_known_limitation(self):
        path = ROOT / "3rd_party/dReal3/dReal"
        if not path.is_file():
            self.skipTest("repository native binary absent")
        runtime._SUCCESS_CACHE.clear()
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            result = runtime.validate_dreal_runtime(path)
        self.assertEqual(len(caught), 0)
        self.assertFalse(result["zero_derivative_forall"])
        self.assertTrue(result["known_limitations"])

    def test_compatible_external_build_passes(self):
        path = Path(os.environ.get("STLMC_TEST_DREAL_COMPATIBLE", "/usr/local/bin/dReal"))
        if not path.is_file():
            self.skipTest("compatible external binary absent")
        self.assertTrue(runtime.validate_dreal_runtime(path)["zero_derivative_forall"])


if __name__ == "__main__":
    unittest.main()
