import random
import unittest

import sympy
import z3

from stlmc.constraints.constraints import (
    Add, Div, Eq, Forall, Function, Int, Integral, Mul, Pow, Real, RealVal, Sin, Sub,
)
from stlmc.constraints.differentiation import differentiate_polynomial, diff_aux
from stlmc.constraints.sympy_expression import SympyExpression
from stlmc.exceptions import NotSupportedError
from stlmc.solver.z3 import z3Obj


class SympyDifferentiationTest(unittest.TestCase):
    def assert_equivalent(self, actual, expected):
        solver = z3.Solver()
        solver.set(timeout=3000)
        solver.add(z3Obj(actual) != z3Obj(expected))
        self.assertEqual(solver.check(), z3.unsat)

    def test_exact_rational_round_trip(self):
        context = SympyExpression()
        x = Real('x')
        expression = Add(Mul(RealVal('0.1'), x), Mul(RealVal('0.2'), x))
        value = context.to_sympy(expression)
        self.assertFalse(value.atoms(sympy.Float))
        self.assert_equivalent(context.from_sympy(value), Div(Mul(RealVal('3'), x), RealVal('10')))
        self.assert_equivalent(differentiate_polynomial(expression, x), Div(RealVal('3'), RealVal('10')))

    def test_typed_same_name_symbols_do_not_alias(self):
        context = SympyExpression()
        real, integer = Real('same'), Int('same')
        self.assertNotEqual(context.symbol(real), context.symbol(integer))
        self.assertIs(context.from_sympy(context.symbol(real)), real)
        self.assertIs(context.from_sympy(context.symbol(integer)), integer)

    def test_only_selected_clock_advances(self):
        end, start = Real('tau_3'), Real('tau_2')
        local = Sub(end, start)
        expression = Pow(local, RealVal('2'))
        self.assert_equivalent(differentiate_polynomial(expression, end), Mul(RealVal('2'), local))
        self.assert_equivalent(diff_aux(expression), RealVal('0'))

    def test_zero_powers_are_normalized_before_solver_translation(self):
        context = SympyExpression()
        # Z3 real-power leaves 0**0 underspecified. Polynomial x**0 must
        # become 1 before endpoint evaluation, including at local time zero.
        result = context.from_sympy(context.to_sympy(Pow(Real('s'), RealVal('0'))))
        self.assert_equivalent(result, RealVal('1'))

    def test_power_flow_cannot_be_constant_over_nonempty_interval(self):
        # x(s)=1.99-s*s/2 is not identically 1.99 on (0,1). The old
        # repeated derivative left s**0 at zero and could accept this case.
        start, end, x = Real('tau_0'), Real('tau_1'), Real('x_0_0')
        local = Sub(end, start)
        expression = Sub(x, Mul(RealVal('0.5'), Pow(local, RealVal('2'))))
        integral = Integral(0, [Real('x_0_t')], [x], Function([x], [expression]))
        condition = Forall(0, end, start, Eq(x, RealVal('1.99')), integral)
        solver = z3.Solver()
        solver.add(z3Obj(condition), z3Obj(start) == 0, z3Obj(end) == 1,
                   z3Obj(x) == z3.RealVal('1.99'), z3.Real('currentMode_0') == 0)
        self.assertEqual(solver.check(), z3.unsat)

    def test_does_not_cancel_clock_denominator_before_validation(self):
        time = Real('elapsed')
        for expression in (Div(time, time), Pow(time, RealVal('-1')),
                           Pow(time, RealVal('0.5')), Sin(time)):
            with self.subTest(expression=str(expression)):
                with self.assertRaises(NotSupportedError):
                    differentiate_polynomial(expression, time)

    def test_zero_denominator_is_explicit_error(self):
        with self.assertRaisesRegex(NotSupportedError, 'zero denominator'):
            differentiate_polynomial(Div(Real('s'), RealVal('0')), Real('s'))

    def test_unsupported_arithmetic_is_not_silently_evaluated(self):
        with self.assertRaisesRegex(NotSupportedError, 'unsupported expression.*Sin'):
            SympyExpression().to_sympy(Sin(Real('s')))

    def test_generated_polynomials_against_analytic_coefficients(self):
        rng = random.Random(1701)
        time, start, initial = Real('tau_3'), Real('tau_2'), Real('d_2_0')
        local = Sub(time, start)
        for case in range(100):
            coefficients = [initial]
            for degree in range(1, rng.randrange(2, 7)):
                parameter = Add(initial, Mul(RealVal(str(rng.randrange(-3, 4))), start))
                coefficients.append(Div(Mul(RealVal(str(rng.randrange(-5, 6))), parameter), RealVal('7')))
            expression = RealVal('0')
            for degree, coefficient in enumerate(coefficients):
                expression = Add(expression, Mul(coefficient, Pow(local, RealVal(str(degree)))))
            actual = expression
            for order in range(1, 4):
                actual = differentiate_polynomial(actual, time)
                expected = RealVal('0')
                for degree in range(order, len(coefficients)):
                    multiplier = 1
                    for offset in range(order):
                        multiplier *= degree-offset
                    power = (RealVal('1') if degree == order else
                             Pow(local, RealVal(str(degree-order))))
                    term = Mul(Mul(RealVal(str(multiplier)), coefficients[degree]), power)
                    expected = Add(expected, term)
                with self.subTest(case=case, order=order):
                    self.assert_equivalent(actual, expected)


if __name__ == '__main__':
    unittest.main()
