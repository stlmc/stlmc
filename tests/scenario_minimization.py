import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.constraints import (
    And, Bool, BoolVal, Eq, Gt, Leq, Or, Real, RealVal,
)
from stlmc.encoding.batching import candidate_batch_formula
from stlmc.encoding.enumerate import (
    assert_and_track_assignment, evaluated_arithmetic_literals,
)
from stlmc.solver.abstract_solver import SolverStatus
from stlmc.solver.z3 import Z3FormulaSolver


class ScenarioMinimizationPolarityTest(unittest.TestCase):
    false = BoolVal("False")

    def test_false_boolean_literal_keeps_its_polarity(self):
        solver = Z3FormulaSolver()
        proposition = Bool("proposition")
        literal = assert_and_track_assignment(
            solver, proposition, self.false, "boolean-false"
        )
        solver.add(proposition)
        self.assertEqual(literal, Eq(proposition, self.false))
        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        self.assertIn("boolean-false", solver.unsat_core())

    def test_false_arithmetic_literal_is_available_to_the_core(self):
        solver = Z3FormulaSolver("QF_LRA")
        x = Real("x")
        clause = Gt(x, RealVal("0"))
        literal = assert_and_track_assignment(
            solver, clause, self.false, "arithmetic-false"
        )
        solver.add(clause)
        self.assertEqual(literal, Eq(clause, self.false))
        self.assertEqual(solver.check(), SolverStatus.UNSAT)
        self.assertIn("arithmetic-false", solver.unsat_core())

    def test_concrete_scenario_keeps_arithmetic_clause_polarity(self):
        x = Real("x")
        clause = Gt(x, RealVal("0"))
        solver = Z3FormulaSolver("QF_LRA")
        solver.add(Leq(x, RealVal("0")))
        self.assertEqual(solver.check(), SolverStatus.SAT)
        literals = evaluated_arithmetic_literals({clause}, {x}, solver.model())
        self.assertEqual(literals, [Eq(clause, self.false)])

    def test_candidate_batch_factors_shared_constraints(self):
        common = Bool("common")
        first = Bool("first")
        second = Bool("second")
        batch = candidate_batch_formula([
            (common, first),
            (common, second),
        ])
        self.assertEqual(
            repr(batch), repr(And([common, Or([first, second])]))
        )

    def test_candidate_batch_preserves_distinct_constraints(self):
        common_a = Bool("common-a")
        common_b = Bool("common-b")
        first = Bool("first")
        second = Bool("second")
        batch = candidate_batch_formula([
            (common_a, first),
            (common_b, second),
        ])
        self.assertEqual(repr(batch), repr(Or([
            And([common_a, first]),
            And([common_b, second]),
        ])))


if __name__ == "__main__":
    unittest.main()
