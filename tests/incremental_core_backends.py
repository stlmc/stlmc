"""Exact incremental adapter contracts; optional native backends may skip."""

import os
from pathlib import Path
import sys
import subprocess
import unittest
from fractions import Fraction
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from stlmc.constraints.constraints import (
    And, Bool, BoolVal, Div, Eq, Geq, Gt, Int, IntVal, Lt, Not, Real, RealVal,
)
from stlmc.solver.abstract_solver import SolverStatus
from stlmc.solver.solver_factory import SolverFactory
from stlmc.exceptions import SolverUnavailableError
from stlmc.utils.interrupt import (
    StlmcInterrupted, clear_interrupt, request_interrupt,
)


class BackendContract:
    def factory(self):
        try:
            factory = SolverFactory().generate_formula_solver_factory(self.backend)
            factory()
        except (SolverUnavailableError, ImportError, OSError) as error:
            self.skipTest(str(error))
        return factory

    def test_exact_model_and_eval(self):
        s = self.factory()()
        x, n, p = Real("same"), Int("integer"), Bool("flag")
        value = "123456789012345678901234567891/987654321098765432109876543219"
        s.add(Eq(x, RealVal(value)))
        s.add(Eq(n, IntVal("-3")))
        s.add(Not(p))
        self.assertEqual(s.check(), SolverStatus.SAT)
        model = s.model()
        self.assertEqual(Fraction(model.get_assignments()[x].value), Fraction(value))
        self.assertEqual(Fraction(model.eval(x).value), Fraction(value))
        self.assertEqual(model.eval(Gt(x, RealVal("0"))), BoolVal("True"))
        self.assertEqual(model.eval(n), IntVal("-3"))
        self.assertEqual(model.eval(p), BoolVal("False"))

    def test_conditional_core_replay_and_false_polarities(self):
        factory = self.factory()
        s = factory()
        a, p = Bool("rho^aux"), Bool("signal")
        x = Real("clock")
        background = Not(And([a, Not(p), Not(Gt(x, RealVal("0")))]))
        s.add(background)
        assignment = Eq(a, BoolVal("True"))
        s.add(assignment)
        literals = {"false-boolean": Eq(p, BoolVal("False")),
                    "false-arithmetic": Eq(Gt(x, RealVal("0")), BoolVal("False"))}
        for key, literal in literals.items():
            s.track(literal, key)
        self.assertEqual(s.check(), SolverStatus.UNSAT)
        core = s.unsat_core()
        self.assertEqual(core, set(literals))
        from stlmc.solver.z3 import Z3FormulaSolver
        replay = Z3FormulaSolver()
        replay.add(background)
        replay.add(assignment)
        for key in core:
            replay.add(literals[key])
        self.assertEqual(replay.check(), SolverStatus.UNSAT)
        replay = Z3FormulaSolver()
        replay.add(background)
        for key in core:
            replay.add(literals[key])
        self.assertEqual(replay.check(), SolverStatus.SAT)

    def test_scopes_active_variables_duplicate_ids_and_fork(self):
        s = self.factory()()
        p, old = Bool("p"), Bool("rho^old")
        s.add(p)
        s.track(p, "outer")
        s.push()
        with self.assertRaisesRegex(ValueError, "duplicate"):
            s.track(Not(p), "outer")
        s.push()
        s.add(old)
        s.track(Not(p), "inner")
        self.assertEqual(s.check(), SolverStatus.UNSAT)
        fork = s.fork()
        self.assertEqual(fork.check(), SolverStatus.UNSAT)
        self.assertIn("inner", fork.unsat_core())
        s.pop()
        self.assertEqual(s.check(), SolverStatus.SAT)
        self.assertEqual(set(s.model().get_assignments()), {p})
        s.track(Not(p), "inner")
        self.assertEqual(s.check(), SolverStatus.UNSAT)
        s.pop()
        self.assertEqual(s.check(), SolverStatus.SAT)
        self.assertEqual(fork.check(), SolverStatus.UNSAT)

    def test_private_guards_and_independent_native_instances(self):
        factory = self.factory()
        first, second = factory(), factory()
        # Same display name, different sorts, in distinct native instances.
        first.add(Eq(Real("shared"), RealVal("1/3")))
        second.add(Eq(Int("shared"), IntVal("2")))
        guard_like = Bool("__stlmc_track_user")
        first.add(Not(guard_like))
        first.track(BoolVal("True"), "user")
        second.track(BoolVal("True"), "user")
        self.assertEqual(first.check(), SolverStatus.SAT)
        self.assertEqual(second.check(), SolverStatus.SAT)
        self.assertEqual(first.model().eval(guard_like), BoolVal("False"))
        self.assertEqual(set(first.model().get_assignments()), {Real("shared"), guard_like})
        self.assertEqual(second.model().eval(Int("shared")), IntVal("2"))

    def test_empty_core_and_interrupt_checkpoints(self):
        s = self.factory()()
        s.add(BoolVal("False"))
        self.assertEqual(s.check(), SolverStatus.UNSAT)
        self.assertEqual(s.unsat_core(), set())
        request_interrupt()
        try:
            with self.assertRaises(StlmcInterrupted):
                s.check()
            with self.assertRaises(StlmcInterrupted):
                s.track(BoolVal("True"), "interrupted")
        finally:
            clear_interrupt()

    def test_unknown_and_mutation_invalidate_results(self):
        s = self.factory()()
        s.add(BoolVal("True"))
        self.assertEqual(s.check(), SolverStatus.SAT)
        with self.assertRaises(ValueError):
            s.unsat_core()
        s.push()
        with self.assertRaises(ValueError):
            s.model()
        if self.backend == "z3":
            import z3
            target, attr, unknown = s._solver, "check", z3.unknown
        else:
            target, attr, unknown = s, "_check", SolverStatus.UNKNOWN
        with mock.patch.object(target, attr, return_value=unknown):
            self.assertEqual(s.check(), SolverStatus.UNKNOWN)
        with self.assertRaises(ValueError):
            s.model()
        with self.assertRaises(ValueError):
            s.unsat_core()

    def test_mixed_integer_real_and_integer_division(self):
        factory = self.factory()
        n, x = Int("mode"), Real("clock")
        solver = factory()
        solver.add(And([Gt(n, IntVal("0")), Lt(n, IntVal("1"))]))
        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        solver = factory()
        solver.add(And([Eq(n, IntVal("2")), Eq(x, RealVal("1/3")),
                        Gt(n + x, RealVal("2"))]))
        self.assertEqual(solver.check(), SolverStatus.SAT)
        for numerator, denominator, quotient in ((3, 2, 1), (-3, 2, -2),
                                                 (3, -2, -1), (-3, -2, 2)):
            with self.subTest(numerator=numerator, denominator=denominator):
                solver = factory()
                integer = Div(IntVal(str(numerator)), IntVal(str(denominator)))
                real = Div(RealVal(str(numerator)), RealVal(str(denominator)))
                solver.add(Not(And([Eq(integer, IntVal(str(quotient))),
                                    Eq(real, RealVal(str(Fraction(numerator, denominator))))])))
                self.assertEqual(solver.check(), SolverStatus.UNSAT)

    def test_scientific_real_constants_are_exact(self):
        for text in ("1e-3", "-3.125e-7", "1.234567890123456789e80"):
            with self.subTest(text=text):
                solver = self.factory()()
                x = Real("scientific")
                solver.add(Eq(x, RealVal(text)))
                self.assertEqual(solver.check(), SolverStatus.SAT)
                self.assertEqual(Fraction(solver.model().eval(x).value), Fraction(text))

    def test_push_after_unsat_restores_parent_assumptions_and_background(self):
        for tracked in (False, True):
            solver = self.factory()()
            p = Bool("p")
            solver.add(p)
            solver.push()
            if tracked:
                solver.track(Not(p), "conflict")
            else:
                solver.add(BoolVal("False"))
            self.assertEqual(solver.check(), SolverStatus.UNSAT)
            solver.push()
            solver.add(Bool("child"))
            solver.track(Bool("child"), "child")
            solver.push()
            self.assertEqual(solver.check(), SolverStatus.UNSAT)
            core = solver.unsat_core()
            self.assertEqual(core, {"conflict"} if tracked else set())
            solver.pop()
            solver.pop()
            self.assertEqual(solver.check(), SolverStatus.UNSAT)
            solver.pop()
            self.assertEqual(solver.check(), SolverStatus.SAT)
            self.assertEqual(set(solver.model().get_assignments()), {p})

    def test_unsat_child_assertions_do_not_pollute_parent_core_background(self):
        solver = self.factory()()
        p, q = Bool("parent-p"), Bool("parent-q")
        solver.add(Not(p))
        solver.add(q)
        solver.track(Not(q), "t")
        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        solver.push()
        solver.add(p)
        solver.track(p, "child")
        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        solver.pop()
        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        self.assertEqual(solver.unsat_core(), {"t"})


class Z3Contract(BackendContract, unittest.TestCase):
    backend = "z3"

    def test_user_can_reuse_the_actual_private_guard_display_name(self):
        solver = self.factory()()
        solver.track(BoolVal("True"), "t")
        guard = solver._track_guards["t"]
        user_variable = Bool(str(guard))
        solver.add(Not(user_variable))
        self.assertEqual(solver.check(), SolverStatus.SAT)
        self.assertEqual(solver.model().eval(user_variable), BoolVal("False"))


class YicesContract(BackendContract, unittest.TestCase):
    backend = "yices"

    def test_native_resources_are_released(self):
        import gc
        factory = self.factory()
        from yices import Config, Context, Model
        gc.collect()
        before = (Config.population(), Context.population(), Model.population())
        for _ in range(20):
            solver = factory()
            solver.add(Bool("lifetime"))
            self.assertEqual(solver.check(), SolverStatus.SAT)
            model = solver.model()
            del solver
            self.assertEqual(model.eval(Bool("lifetime")), BoolVal("True"))
            del model
        gc.collect()
        self.assertEqual((Config.population(), Context.population(), Model.population()), before)
        with mock.patch.object(Config, "default_config_for_logic", side_effect=RuntimeError("invalid logic")):
            with self.assertRaisesRegex(RuntimeError, "invalid logic"):
                factory()
        gc.collect()
        self.assertEqual((Config.population(), Context.population(), Model.population()), before)


class CVC5Contract(BackendContract, unittest.TestCase):
    backend = "cvc5"

    def test_cvc5_does_not_require_optional_yices_import(self):
        self.factory()
        script = '''
import importlib
original_import = importlib.import_module
def unavailable_yices(name, package=None):
    if name == 'yices':
        raise RuntimeError('optional native library missing')
    return original_import(name, package)
importlib.import_module = unavailable_yices
from stlmc.solver.cvc5 import CVC5FormulaSolver
from stlmc.constraints.constraints import BoolVal
from stlmc.solver.abstract_solver import SolverStatus
solver = CVC5FormulaSolver()
solver.add(BoolVal('True'))
assert solver.check() is SolverStatus.SAT
'''
        env = dict(os.environ, PYTHONPATH=str(Path(__file__).resolve().parent.parent/'src'))
        result = subprocess.run([sys.executable, '-c', script], env=env,
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


class FactorySelectionTest(unittest.TestCase):
    def test_env_roles_are_independent_and_core_defaults_to_z3(self):
        for backend in ("cvc5", "yices"):
            try:
                SolverFactory().generate_formula_solver_factory(backend)
            except SolverUnavailableError as error:
                self.skipTest(str(error))
        with mock.patch.dict(os.environ, {"STLMC_SCENARIO_SOLVER": "cvc5"}, clear=True):
            f = SolverFactory()
            self.assertEqual(f.generate_formula_solver_factory().__name__, "CVC5FormulaSolver")
            self.assertEqual(f.generate_formula_solver_factory(role="core").__name__, "Z3FormulaSolver")
        with mock.patch.dict(os.environ, {"STLMC_SCENARIO_SOLVER": "z3", "STLMC_CORE_SOLVER": "yices"}):
            self.assertEqual(f.generate_formula_solver_factory(role="core").__name__, "YicesFormulaSolver")

    def test_unknown_backend_is_explicit(self):
        with self.assertRaisesRegex(SolverUnavailableError, "unknown internal core solver"):
            SolverFactory().generate_formula_solver_factory("missing", role="core")

    def test_native_import_failure_has_role_and_install_hint(self):
        with mock.patch("importlib.import_module", side_effect=RuntimeError("native library absent")):
            with self.assertRaisesRegex(SolverUnavailableError, "yices.*core.*stlmc-install-solvers yices"):
                SolverFactory().generate_formula_solver_factory("yices", role="core")

    def test_legacy_no_argument_scenario_override_does_not_select_core(self):
        class LegacyFactory(SolverFactory):
            def generate_formula_solver_factory(self):
                return "custom-scenario"
        with mock.patch.dict(os.environ, {"STLMC_CORE_SOLVER": "z3"}):
            factory = LegacyFactory()
            self.assertEqual(factory.generate_formula_solver_factory(), "custom-scenario")
            self.assertEqual(factory.generate_core_solver_factory().__name__, "Z3FormulaSolver")


if __name__ == "__main__":
    unittest.main()
