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

    def test_midpoint_remains_inside_a_narrow_interval(self):
        assignment = DrealAssignment([
            "x : Real = [3.486834135780377, 3.48683414884334]",
        ]).get_assignments()

        value = assignment[Real("x")]
        self.assertLessEqual(float(value.lower), float(value.midpoint))
        self.assertLessEqual(float(value.midpoint), float(value.upper))


if __name__ == "__main__":
    unittest.main()
