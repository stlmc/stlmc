"""Availability-aware auto selection does not install or share native state."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))

from stlmc.constraints.constraints import Add, BoolVal, Function, Geq, Mul, Ode, Real, RealVal, Sqrt
from stlmc.exceptions import SolverUnavailableError
from stlmc.objects.goal import StlGoal
from stlmc.parser.config_visitor import ConfigVisitor
from stlmc.solver import auto_selection as auto


def model(flow=None):
    x = Real("x")
    return SimpleNamespace(init=BoolVal("True"), const_dict={}, modules=[{
        "mode": BoolVal("True"), "inv": BoolVal("True"), "jump": {},
        "flow": flow or Function([x], [Add(Real("x_0"), Real("time"))]),
    }])


class AutoSolverTest(unittest.TestCase):
    def setUp(self):
        self.config = ConfigVisitor().parse_from_file(str(ROOT / "src/stlmc/default.cfg"))
        common = self.config.get_section("common")
        common.arguments.update({"bound": "2", "time-bound": "2"})
        self.goals = [StlGoal(Geq(Real("x"), RealVal("0")))]

    def test_exact_priority_then_dreal_fallback(self):
        self.assertEqual(auto.solver_candidates(model(), self.goals, {}),
                         ("z3", "cvc5", "yices", "dreal"))
        for supported in ("z3", "cvc5", "yices", "dreal"):
            probe = mock.Mock(side_effect=lambda name, config: (name == supported, "unavailable"))
            self.assertEqual(auto.select_available_solver(model(), self.goals, {}, self.config, probe), supported)
            self.assertEqual(probe.call_args_list[-1].args[0], supported)

    def test_evolving_state_ode_requires_native_solver(self):
        x = Real("x")
        self.assertEqual(auto.solver_candidates(model(Ode([x], [x])), self.goals, {}), ("dreal",))
        self.assertEqual(auto.solver_candidates(model(Ode([x], [RealVal("1")])), self.goals, {})[0], "z3")

    def test_selected_formula_and_substituted_definitions_are_checked(self):
        goal = StlGoal(Geq(Sqrt(Real("x")), RealVal("0")))
        self.assertEqual(auto.solver_candidates(model(), [goal], {}), ("dreal",))
        self.assertEqual(auto.solver_candidates(model(), self.goals, {})[0], "z3")

    def test_no_usable_candidate_reports_causes_and_does_not_install(self):
        with self.assertRaisesRegex(SolverUnavailableError, "auto could not find.*") as failure:
            auto.select_available_solver(model(), self.goals, {}, self.config,
                                         lambda name, config: (False, "native capability missing"))
        self.assertIn("z3: native capability missing", str(failure.exception))
        self.assertIn("stlmc-installer check", str(failure.exception))

    def test_nonlinear_model_does_not_use_a_requested_linear_logic(self):
        for backend in ("z3", "cvc5", "yices"):
            self.config.get_section(backend).arguments["logic"] = "QF_LRA"
        x = Real("x")
        goals = [StlGoal(Geq(Mul(x, x), RealVal("2")))]
        probe = mock.Mock(return_value=(False, "missing"))
        with self.assertRaisesRegex(SolverUnavailableError, "cannot represent this nonlinear encoding"):
            auto.select_available_solver(model(), goals, {}, self.config, probe)
        self.assertEqual([call.args[0] for call in probe.call_args_list], ["dreal"])
        self.assertEqual(self.config.get_section("cvc5").get_value("logic"), "QF_LRA")

    def test_runtime_probe_is_isolated_and_uses_requested_config(self):
        child = mock.Mock(returncode=0)
        child.communicate.return_value = (auto._MARKER + json.dumps({"available": True, "detail": "ok"}), "")
        self.config.get_section("yices").arguments["logic"] = "QF_LRA"
        with mock.patch.object(auto.subprocess, "Popen", return_value=child) as launch:
            self.assertEqual(auto.probe_solver_runtime("yices", self.config), (True, "ok"))
        command = launch.call_args.args[0]
        self.assertEqual(command[:2], [sys.executable, "-c"])
        self.assertEqual(json.loads(command[-1])["yices"]["logic"], "QF_LRA")
        self.assertEqual(launch.call_args.kwargs["start_new_session"], os.name == "posix")

    def test_bad_or_missing_capability_reports_are_rejected(self):
        for output in ("", auto._MARKER + "[]", auto._MARKER + '{"available":"yes"}'):
            child = mock.Mock(returncode=0)
            child.communicate.return_value = (output, "")
            with self.subTest(output=output), mock.patch.object(auto.subprocess, "Popen", return_value=child):
                self.assertFalse(auto.probe_solver_runtime("z3", self.config)[0])

    def test_dreal_uses_the_native_supervisor_without_nesting_process_groups(self):
        with mock.patch('stlmc.solver.dreal_runtime.validate_dreal_runtime',
                        return_value={"version": "dReal v3.test"}) as validate, \
                mock.patch.object(auto, "find_dreal", return_value="/native/dReal"), \
                mock.patch.object(auto.subprocess, "Popen") as launch:
            self.assertTrue(auto.probe_solver_runtime("dreal", self.config)[0])
            validate.assert_called_once_with("/native/dReal")
            launch.assert_not_called()

    def test_native_crash_and_timeout_are_reported(self):
        child = mock.Mock(returncode=-11, pid=12345)
        child.communicate.return_value = ("", "native crash")
        with mock.patch.object(auto.subprocess, "Popen", return_value=child):
            self.assertIn("-11", auto.probe_solver_runtime("z3", self.config)[1])
        child.communicate.side_effect = [subprocess.TimeoutExpired("probe", 25), ("", "")]
        with mock.patch.object(auto.subprocess, "Popen", return_value=child), mock.patch.object(auto.os, "killpg", create=True) as kill:
            self.assertEqual(auto.probe_solver_runtime("z3", self.config), (False, "runtime probe timed out"))
            if os.name == "posix":
                kill.assert_called_once_with(12345, auto.signal.SIGKILL)

    def test_real_available_z3_and_selected_goal_only(self):
        if not auto.probe_solver_runtime("z3", self.config)[0]:
            self.skipTest("optional Z3 unavailable")
        with tempfile.TemporaryDirectory(dir=ROOT / ".tmp", prefix="auto-solver-") as directory:
            work = Path(directory)
            (work / "case.model").write_text('''[0,3] x;
{ mode: true; inv: x <= 3; flow: x(t) = x(0) + t; jump: }
init: x = 0;
proposition:
goal:
[safe]: [][0,2] x <= 1;
[root]: sqrt(x) >= 0;
''')
            environment = dict(os.environ, PYTHONPATH=str(ROOT / "src"), STLMC_DISABLE_UPDATE_CHECK="1", OPENBLAS_NUM_THREADS="1")
            result = subprocess.run([sys.executable, "-c", "from stlmc.cli.mc import main; raise SystemExit(main())",
                                     str(work / "case.model"), "-goal", "safe", "-bound", "2", "-time-bound", "2"],
                                    cwd=work, env=environment, capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertRegex(result.stdout, r"solver\s*:\s*z3")
            self.assertRegex(result.stdout, r"status\s*:\s*violated")

    def test_auto_cli_overrides_reach_all_candidate_sections(self):
        from stlmc.cli.command import CliCommand
        with tempfile.TemporaryDirectory(dir=ROOT / ".tmp", prefix="auto-config-") as directory:
            path = Path(directory) / "case.model"
            path.touch()
            arguments = ["stlmc", str(path), "-bound", "2", "-time-bound", "2", "-solver", "auto",
                         "-logic", "QF_LRA", "-executable-path", "/custom/dReal"]
            with mock.patch.object(sys, "argv", arguments):
                command = CliCommand()
                command.parse()
            for backend in ("z3", "yices", "cvc5"):
                self.assertEqual(command.config.get_section(backend).get_value("logic"), "QF_LRA")
            self.assertEqual(command.config.get_section("dreal").get_value("executable-path"), "/custom/dReal")


if __name__ == "__main__":
    unittest.main()
