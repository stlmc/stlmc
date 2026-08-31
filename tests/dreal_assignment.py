import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.constraints import Bool, Real
from stlmc.solver.dreal import DrealAssignment, DrealInterval


class DrealAssignmentTest(unittest.TestCase):
    def test_preserves_interval_box_and_midpoint(self):
        assignment = DrealAssignment([
            "x : Real = [1.25, 1.75]",
            "enabled : Bool = true",
        ]).get_assignments()

        value = assignment[Real("x")]
        self.assertIsInstance(value, DrealInterval)
        self.assertEqual(value.lower, "1.25")
        self.assertEqual(value.upper, "1.75")
        self.assertEqual(float(value.midpoint), 1.5)
        self.assertEqual(assignment[Bool("enabled")].value, "True")

    def test_tau_interval_is_not_reconstructed_from_dead_duration_state(self):
        assignment = DrealAssignment([
            "tau_1 : Real = [2.0, 2.2]",
        ]).get_assignments()

        self.assertEqual(assignment[Real("tau_1")].lower, "2.0")
        self.assertEqual(assignment[Real("tau_1")].upper, "2.2")


if __name__ == "__main__":
    unittest.main()
