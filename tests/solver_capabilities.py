import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.constraints import (
    Arccos, Arcsin, Arctan, Cos, Pow, Real, RealVal, Sin, Sqrt, Tan,
)
from stlmc.exception.exception import NotSupportedError
from stlmc.solver.capability import (
    expression_requires_dreal,
    validate_formula_solver_support,
)
from stlmc.solver.dreal import drealObj
from stlmc.solver.new_dreal import dreal_obj


class SolverCapabilityTest(unittest.TestCase):
    def test_z3_and_yices_reject_transcendental_arithmetic(self):
        x = Real("x")
        expressions = (
            Sqrt(x), Sin(x), Cos(x), Tan(x),
            Arcsin(x), Arccos(x), Arctan(x),
        )
        for solver in ("z3", "yices"):
            for expression in expressions:
                with self.subTest(solver=solver, expression=expression):
                    with self.assertRaisesRegex(
                        NotSupportedError, "use dReal"
                    ):
                        validate_formula_solver_support(solver, expression)

    def test_z3_and_yices_accept_only_integer_constant_powers(self):
        x = Real("x")
        for solver in ("z3", "yices"):
            validate_formula_solver_support(
                solver, Pow(x, RealVal("2"))
            )
            for exponent in (RealVal("0.5"), RealVal("-1"), x):
                with self.subTest(solver=solver, exponent=exponent):
                    with self.assertRaisesRegex(
                        NotSupportedError, "non-negative integer"
                    ):
                        validate_formula_solver_support(
                            solver, Pow(x, exponent)
                        )

    def test_dreal_inverse_trigonometric_names(self):
        x = Real("x")
        expected = {
            Arcsin(x): "(asin x)",
            Arccos(x): "(acos x)",
            Arctan(x): "(atan x)",
        }
        for expression, output in expected.items():
            with self.subTest(expression=expression):
                self.assertEqual(drealObj(expression), output)
                self.assertEqual(dreal_obj(expression), output)

    def test_auto_solver_detects_nested_dreal_arithmetic(self):
        x = Real("x")
        self.assertTrue(expression_requires_dreal(Cos(Sqrt(x))))
        self.assertTrue(
            expression_requires_dreal(Pow(x, RealVal("0.5")))
        )
        self.assertFalse(expression_requires_dreal(Pow(x, RealVal("2"))))


if __name__ == "__main__":
    unittest.main()
