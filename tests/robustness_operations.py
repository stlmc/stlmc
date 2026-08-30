import sys
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.robustness import release_robustness, until_robustness
from stlmc.constraints.constraints import (
    Add, And, Eq, Geq, Gt, Implies, Leq, Lt, Neq, Not, Or, Real, RealVal, Sub,
)
from stlmc.constraints.operations import relaxing, strengthening


class RobustnessOperationsTest(unittest.TestCase):
    def setUp(self):
        self.x = Real("x")
        self.zero = RealVal("0")
        self.epsilon = RealVal("0.5")

    def test_atomic_weakening_matches_maude_rules(self):
        self.assertEqual(relaxing(Gt(self.x, self.zero), 0.5),
                         Gt(self.x, Sub(self.zero, self.epsilon)))
        self.assertEqual(relaxing(Lt(self.x, self.zero), 0.5),
                         Lt(self.x, Add(self.zero, self.epsilon)))
        self.assertEqual(relaxing(Eq(self.x, self.zero), 0.5), And([
            Geq(self.x, Sub(self.zero, self.epsilon)),
            Leq(self.x, Add(self.zero, self.epsilon)),
        ]))
        self.assertEqual(relaxing(Neq(self.x, self.zero), 0.5), Or([
            Lt(self.x, Add(self.zero, self.epsilon)),
            Gt(self.x, Sub(self.zero, self.epsilon)),
        ]))

    def test_atomic_strengthening_matches_maude_rules(self):
        self.assertEqual(strengthening(Gt(self.x, self.zero), 0.5),
                         Gt(self.x, Add(self.zero, self.epsilon)))
        self.assertEqual(strengthening(Lt(self.x, self.zero), 0.5),
                         Lt(self.x, Sub(self.zero, self.epsilon)))
        self.assertEqual(strengthening(Neq(self.x, self.zero), 0.5), Or([
            Lt(self.x, Sub(self.zero, self.epsilon)),
            Gt(self.x, Add(self.zero, self.epsilon)),
        ]))

    def test_negation_reverses_polarity(self):
        atom = Lt(self.x, self.zero)
        self.assertEqual(relaxing(Not(atom), 0.5),
                         Not(strengthening(atom, 0.5)))
        self.assertEqual(strengthening(Not(atom), 0.5),
                         Not(relaxing(atom, 0.5)))

    def test_implication_antecedent_is_contravariant(self):
        antecedent = Lt(self.x, self.zero)
        consequent = Gt(self.x, self.zero)
        formula = Implies(antecedent, consequent)
        self.assertEqual(relaxing(formula, 0.5), Implies(
            strengthening(antecedent, 0.5), relaxing(consequent, 0.5)
        ))
        self.assertEqual(strengthening(formula, 0.5), Implies(
            relaxing(antecedent, 0.5), strengthening(consequent, 0.5)
        ))

    def test_until_uses_right_operand_at_witness(self):
        times = [0.0, 1.0, 2.0]
        left = {0.0: 2.0, 1.0: 2.0, 2.0: 2.0}
        right = {0.0: -5.0, 1.0: -5.0, 2.0: 3.0}

        value = until_robustness(
            times, lambda witness: [t for t in times if t <= witness],
            left.__getitem__, right.__getitem__,
        )

        self.assertEqual(value, 2.0)

    def test_release_uses_right_operand_at_witness(self):
        times = [0.0, 1.0, 2.0]
        left = {0.0: 3.0, 1.0: -5.0, 2.0: -5.0}
        right = {0.0: -2.0, 1.0: -2.0, 2.0: 4.0}

        value = release_robustness(
            times, lambda witness: [t for t in times if t <= witness],
            left.__getitem__, right.__getitem__,
        )

        self.assertEqual(value, 3.0)


if __name__ == "__main__":
    unittest.main()
