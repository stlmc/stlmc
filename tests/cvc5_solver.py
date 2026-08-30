import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.constraints import And, Geq, Lt, Real, RealVal
from stlmc.parser.config_visitor import ConfigVisitor
from stlmc.solver.cvc5 import CVC5Solver
from stlmc.solver.solver_factory import SolverFactory


class CVC5SolverTest(unittest.TestCase):
    def setUp(self):
        self.config = ConfigVisitor().parse_from_file(
            str(PROJECT_ROOT / "src/stlmc/default.cfg")
        )
        self.config.get_section("common").set_value("solver", "cvc5")

    def test_factory_creates_cvc5_solver(self):
        self.assertIsInstance(
            SolverFactory().generate_solver(self.config), CVC5Solver
        )

    def test_sat_result_contains_assignment(self):
        x = Real("x")
        result = CVC5Solver(self.config).solve(
            And([Geq(x, RealVal("1")), Lt(x, RealVal("2"))]), timeout=5
        )

        self.assertEqual(result.result, "False")
        self.assertIn(x, result.assignment.get_assignments())

    def test_unsat_result(self):
        x = Real("x")
        result = CVC5Solver(self.config).solve(
            And([Geq(x, RealVal("2")), Lt(x, RealVal("1"))]), timeout=5
        )

        self.assertEqual(result.result, "True")


if __name__ == "__main__":
    unittest.main()
