import unittest

from stlmcPy.constraints.constraints import Bool, Real, And, Gt, Lt, RealVal, Or, Not
from stlmcPy.constraints.operations import make_dict, substitution


class ConstOperationTest(unittest.TestCase):

    def test_make_dict(self):
        # mode_dict => key : string, value : object
        # cont_dict => key : object, value : (left_end, left, right, right_end)
        # assumption : object is variable type
        mode_dict = {'mode_a': Bool('mode_a'), 'mode_b': Real('mode_b')}
        cont_dict = {Real('x'): (True, 1.0, 4.0, True), Real('y'): (False, -1.0, 2.3, False)}
        const_dict = {}
        result_dict = make_dict(2, mode_dict, cont_dict, const_dict, suffix="0")
        self.assertEqual(repr(result_dict),
                         '{bool mode_a: bool mode_a_2, real mode_b: real mode_b_2, real x: real x_2_0, real y: real '
                         'y_2_0}', 'Not correct result')

    def test_substitution_case1(self):
        mode_dict = {'mode_a': Bool('mode_a'), 'mode_b': Real('mode_b')}
        cont_dict = {Real('x'): (True, 1.0, 4.0, True), Real('y'): (False, -1.0, 2.3, False)}
        const_dict = {}
        # { bool mode_a: bool mode_a_2, real mode_b: real mode_b_2,
        #   real x: real x_2_0, real y: real y_2_0}
        result_dict = make_dict(2, mode_dict, cont_dict, const_dict, suffix="0")

        # x > 0 and y < mode_b
        const = And([Gt(Real('x'), RealVal('0')), Lt(Real('y'), Real('mode_b'))])

        # ideal: x_2_0 > 0 and y_2_0 < mode_b_2
        # actual: (and (> real x_2_0 0) (< real y_2_0 real mode_b_2))
        result_const = substitution(const, result_dict)
        self.assertEqual(repr(result_const), "(and (> real x_2_0 0) (< real y_2_0 real mode_b_2))",
                         'Not correct result')

    def test_substitution_case2(self):
        mode_dict = {'mode_a': Bool('mode_a'), 'mode_b': Real('mode_b')}
        cont_dict = {Real('x'): (True, 1.0, 4.0, True), Real('y'): (False, -1.0, 2.3, False)}
        const_dict = {}
        # { bool mode_a: bool mode_a_2, real mode_b: real mode_b_2,
        #   real x: real x_2_0, real y: real y_2_0}
        result_dict = make_dict(2, mode_dict, cont_dict, const_dict, suffix="0")

        # x > 0 and (mode_a or y < mode_b)
        const = And([Gt(Real('x'), RealVal('0')), Or([Bool('mode_a'), Lt(Real('y'), Real('mode_b'))])])

        # ideal: x_2_0 > 0 and (mode_a_2 or y_2_0 < mode_b_2)
        # actual: (and (> real x_2_0 0) (or bool mode_a_2 (< real y_2_0 real mode_b_2)))
        result_const = substitution(const, result_dict)
        self.assertEqual(repr(result_const), "(and (> real x_2_0 0) (or bool mode_a_2 (< real y_2_0 real mode_b_2)))",
                         'Not correct result')

    def test_substitution_case3(self):
        mode_dict = {'mode_a': Bool('mode_a'), 'mode_b': Real('mode_b')}
        cont_dict = {Real('x'): (True, 1.0, 4.0, True), Real('y'): (False, -1.0, 2.3, False)}
        const_dict = {}
        # { bool mode_a: bool mode_a_2, real mode_b: real mode_b_2,
        #   real x: real x_2_0, real y: real y_2_0}
        result_dict = make_dict(2, mode_dict, cont_dict, const_dict, suffix="0")

        # x > 0 and (mode_a or y < mode_b)
        const = And([Gt(Real('x'), RealVal('0')), Or([Not(Bool('mode_a')), Lt(Real('y'), Real('mode_b'))])])

        # ideal: x_2_0 > 0 and (not (mode_a_2) or y_2_0 < mode_b_2)
        # actual: (and (> real x_2_0 0) (or bool mode_a_2 (< real y_2_0 real mode_b_2)))
        result_const = substitution(const, result_dict)

        self.assertEqual(repr(result_const), "(and (> real x_2_0 0) (or (not bool mode_a_2) (< real y_2_0 real mode_b_2)))",
                         'Not correct result')
