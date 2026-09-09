import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.application.options import RunOptions
from stlmc.application.result import (
    AlgorithmResult, SearchStatus, interpret_algorithm_result,
)
from stlmc.objects.configuration import Configuration, Section
from stlmc.solver.abstract_solver import SolveResult, SolverStatus


def configuration(**overrides):
    values = {
        "solver": '"z3"', "bound": "3", "time-bound": "10",
        "time-horizon": '"time-bound"', "threshold": "0.01",
        "parallel-core": "2", "solver-batch-size": "4",
        "path-strategy": '"explicit"', "goal": '"all"',
        "two-step": '"true"', "concrete": '"false"',
        "parallel": '"true"', "visualize": '"false"',
        "verbose": '"false"', "reach": '"false"',
        "smt-preprocess": '"true"',
    }
    values.update(overrides)
    result = Configuration()
    common = Section()
    common.name = "common"
    common.arguments = values
    result.add_section(common)
    return result


class ApplicationBoundaryTest(unittest.TestCase):
    def test_configuration_is_typed_once_at_application_boundary(self):
        options = RunOptions.from_configuration(configuration())
        self.assertEqual(options.bound, 3)
        self.assertEqual(options.time_horizon, 10.0)
        self.assertTrue(options.parallel)
        self.assertEqual(options.goal_labels, ())

    def test_search_result_has_property_independent_meaning(self):
        result = AlgorithmResult(
            SearchStatus.WITNESS_FOUND, 0.1, 2, {"x": 1}, "False"
        )
        self.assertEqual(interpret_algorithm_result(result, False).status, "violated")
        self.assertEqual(interpret_algorithm_result(result, True).status, "reachable")
        self.assertEqual(tuple(result)[0], "False")
        self.assertEqual(result[0], "False")
        self.assertEqual(result[-1], {"x": 1})
        self.assertEqual(len(result), 4)

    def test_solver_result_exposes_typed_status_compatibly(self):
        self.assertIs(SolveResult("False", None).status, SolverStatus.SAT)
        self.assertIs(SolveResult("True", None).status, SolverStatus.UNSAT)
        self.assertIs(SolveResult("Unknown", None).status, SolverStatus.UNKNOWN)
        typed = SolveResult(SolverStatus.SAT, None)
        self.assertEqual(typed.result, "False")


if __name__ == "__main__":
    unittest.main()
