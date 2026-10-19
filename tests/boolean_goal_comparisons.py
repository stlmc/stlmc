"""Boolean goal comparisons preserve proposition and state-variable meaning."""

from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))

from stlmc.constraints.constraints import Bool, BoolVal, Not
from stlmc.constraints.substitution import substitution
from stlmc.exceptions import NotSupportedError
from stlmc.parser.model_visitor import ModelVisitor


class BooleanGoalComparisonTest(unittest.TestCase):
    def parse(self, goal, proposition='ix', declarations=''):
        source = '''%s
bool ix;
[-2,2] x;
{ mode: true; inv: true; flow: d/dt[x] = 0;
  jump: true => (x' = x); }
init: and (x = 0) (ix = false);
proposition: [pix]: %s;
goal: [test]: %s;
''' % (declarations, proposition, goal)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'boolean.model'
            path.write_text(source)
            _, definitions, goals, _ = ModelVisitor().get_parse_tree(str(path))
        formula = goals[0][0]
        return formula, substitution(formula, definitions)

    def test_alias_boolean_literals_both_orders_and_operators(self):
        for literal in ('true', 'false'):
            for operator in ('=', '!='):
                positive = (literal == 'true') == (operator == '=')
                expected = Bool('pix') if positive else Not(Bool('pix'))
                for left, right in (('pix', literal), (literal, 'pix')):
                    with self.subTest(left=left, operator=operator, right=right):
                        formula, _ = self.parse('{} {} {}'.format(left, operator, right))
                        self.assertEqual(formula, expected)

    def test_declared_boolean_literal_comparisons(self):
        for literal in ('true', 'false'):
            for operator in ('=', '!='):
                positive = (literal == 'true') == (operator == '=')
                reference = 'ix' if positive else '~ ix'
                for left, right in (('ix', literal), (literal, 'ix')):
                    with self.subTest(left=left, operator=operator, right=right):
                        _, actual = self.parse('{} {} {}'.format(left, operator, right))
                        _, expected = self.parse(reference)
                        self.assertEqual(actual, expected)

    def test_compound_alias_negates_entire_predicate_under_nested_temporals(self):
        for predicate in ('ix', '(and ix (x >= 0))'):
            _, actual = self.parse('<>[0,1] (x <= 1 U[0,1] pix = false)', predicate)
            _, expected = self.parse('<>[0,1] (x <= 1 U[0,1] ~ pix)', predicate)
            self.assertEqual(actual, expected)

    def test_numeric_comparisons_keep_existing_atomic_predicates(self):
        for operator in ('=', '!=', '<', '<=', '>', '>='):
            with self.subTest(operator=operator):
                _, expanded = self.parse('x {} 1'.format(operator))
                self.assertEqual(expanded.left.id, 'x')
                self.assertEqual(expanded.right.value, '1')

    def test_boolean_pair_comparison_matches_explicit_connectives(self):
        for operator, reference in (
                ('=', '((pix and ix) or ((~ pix) and (~ ix)))'),
                ('!=', '((pix and (~ ix)) or ((~ pix) and ix))')):
            with self.subTest(operator=operator):
                _, actual = self.parse('pix {} ix'.format(operator))
                _, expected = self.parse(reference)
                self.assertEqual(actual, expected)

    def test_boolean_literal_pairs_follow_truth_table(self):
        for left in ('true', 'false'):
            for right in ('true', 'false'):
                for operator in ('=', '!='):
                    expected = (left == right) == (operator == '=')
                    with self.subTest(left=left, right=right, operator=operator):
                        formula, _ = self.parse('{} {} {}'.format(left, operator, right))
                        self.assertEqual(formula, BoolVal(str(expected)))

    def test_boolean_named_constants_remain_formula_values(self):
        for literal in ('true', 'false'):
            for operator in ('=', '!='):
                positive = (literal == 'true') == (operator == '=')
                for left, right in (('flag', literal), (literal, 'flag')):
                    with self.subTest(left=left, right=right, operator=operator):
                        formula, _ = self.parse('{} {} {}'.format(left, operator, right),
                                                declarations='const flag = false;')
                        self.assertEqual(formula, Bool('flag') if positive else Not(Bool('flag')))

    def test_boolean_ordering_and_mixed_scalar_comparisons_are_rejected(self):
        for goal in ('pix < false', 'true >= pix', 'ix > false',
                     'false <= ix', 'x = false', 'true != x',
                     'pix = 1', '0 != ix', 'pix < x'):
            with self.subTest(goal=goal), self.assertRaises(NotSupportedError):
                self.parse(goal)


if __name__ == '__main__':
    unittest.main()
