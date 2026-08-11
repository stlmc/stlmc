import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

import z3

from stlmc.constraints.constraints import Bool, BoolVal, Eq, Gt, Leq, Real, RealVal
from stlmc.encoding.enumerate import (
    assert_and_track_assignment,
    evaluated_arithmetic_literals,
    smaller_unsat_core,
)
from stlmc.solver.z3 import z3Obj


class ScenarioMinimizationPolarityTest(unittest.TestCase):
    false = BoolVal("False")

    def test_false_boolean_literal_keeps_its_polarity(self):
        solver = z3.Solver()
        proposition = Bool("proposition")

        literal = assert_and_track_assignment(
            solver, proposition, self.false, "boolean-false"
        )
        solver.add(z3Obj(proposition))

        self.assertEqual(literal, Eq(proposition, self.false))
        self.assertEqual(solver.check(), z3.unsat)
        self.assertIn("boolean-false", {str(item) for item in solver.unsat_core()})

    def test_false_arithmetic_literal_is_available_to_the_core(self):
        solver = z3.SolverFor("QF_LRA")
        x = Real("x")
        clause = Gt(x, RealVal("0"))

        literal = assert_and_track_assignment(
            solver, clause, self.false, "arithmetic-false"
        )
        solver.add(z3Obj(clause))

        self.assertEqual(literal, Eq(clause, self.false))
        self.assertEqual(solver.check(), z3.unsat)
        self.assertIn("arithmetic-false", {str(item) for item in solver.unsat_core()})

    def test_concrete_scenario_keeps_arithmetic_clause_polarity(self):
        x = Real("x")
        clause = Gt(x, RealVal("0"))
        solver = z3.SolverFor("QF_LRA")
        solver.add(z3Obj(Leq(x, RealVal("0"))))
        self.assertEqual(solver.check(), z3.sat)

        literals = evaluated_arithmetic_literals({clause}, {x}, solver.model())

        self.assertEqual(literals, [Eq(clause, self.false)])

    def test_extra_core_attempts_never_return_a_larger_core(self):
        a = Bool("a")
        b = Bool("b")
        solver = z3.SolverFor("QF_LRA")
        solver.set(":core.minimize", True)
        solver.add(z3.Not(z3.And(z3Obj(a), z3Obj(b))))
        literals = {
            "track-a": Eq(a, BoolVal("True")),
            "track-b": Eq(b, BoolVal("True")),
        }
        for track_id, literal in literals.items():
            solver.assert_and_track(z3Obj(literal), track_id)
        self.assertEqual(solver.check(), z3.unsat)
        initial = {str(item) for item in solver.unsat_core()}

        improved = smaller_unsat_core(solver, literals, initial, attempts=3)

        self.assertLessEqual(len(improved), len(initial))

if __name__ == "__main__":
    unittest.main()
