import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

import z3

from stlmc.constraints.constraints import (
    And, Bool, BoolVal, Eq, Geq, Gt, Leq, Or, Real, RealVal,
)
from stlmc.encoding.batching import candidate_batch_formula
from stlmc.encoding.enumerate import (
    assert_and_track_assignment, boolean_core_assignments,
    evaluated_arithmetic_literals, relevant_boolean_abstract_links,
)
from stlmc.solver.abstract_solver import SolverStatus
from stlmc.solver.z3 import Z3FormulaSolver, z3Obj


class ScenarioMinimizationPolarityTest(unittest.TestCase):
    false = BoolVal("False")

    def test_slicing_keeps_boolean_dependency_closure(self):
        a, b, c, unused = (Bool(name) for name in ("a", "b", "c", "unused"))
        links = relevant_boolean_abstract_links(
            {a: b, b: c, c: BoolVal("True"), unused: BoolVal("False")},
            a,
        )

        text = str(links)
        self.assertIn("(a = b)", text)
        self.assertIn("(b = c)", text)
        self.assertIn("(c = True)", text)
        self.assertNotIn("unused", text)

    def test_slicing_inlines_boolean_core_assignments(self):
        a, b = Bool("a"), Bool("b")
        assignments = boolean_core_assignments(
            And([Eq(a, BoolVal("True")), Eq(b, BoolVal("False"))])
        )
        links = relevant_boolean_abstract_links(
            {
                a: Geq(Real("x"), RealVal("0")),
                b: Leq(Real("y"), RealVal("1")),
            },
            And([a, b]),
            assignments,
        )

        text = str(links)
        self.assertIn("(x >= 0)", text)
        self.assertIn("(not (y <= 1))", text)
        self.assertNotIn("(a =", text)
        self.assertNotIn("(b =", text)

    def test_preprocessing_is_existentially_equivalent(self):
        a, b, c, unused = (Bool(name) for name in ("a", "b", "c", "unused"))
        x = Real("x")
        abstraction = {
            a: Geq(x, RealVal("0")),
            b: c,
            c: Leq(x, RealVal("2")),
            unused: Geq(x, RealVal("100")),
        }
        roots = And([
            Eq(a, BoolVal("True")),
            Eq(b, BoolVal("False")),
        ])
        assignments = boolean_core_assignments(roots)
        original = And([
            roots,
            And([
                Eq(variable, definition)
                for variable, definition in abstraction.items()
            ]),
        ])
        preprocessed = And([
            roots,
            relevant_boolean_abstract_links(
                abstraction, roots, assignments
            ),
        ])

        abstract_variables = [z3Obj(variable) for variable in abstraction]
        solver = z3.Solver()
        solver.add(z3.Xor(
            z3.Exists(abstract_variables, z3Obj(original)),
            z3.Exists(abstract_variables, z3Obj(preprocessed)),
        ))

        self.assertEqual(solver.check(), z3.unsat)

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
