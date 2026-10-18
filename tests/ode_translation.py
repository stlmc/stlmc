"""Exact polynomial ODE lowering, independently checked analytically."""
import unittest
import sympy

from stlmc.constraints.constraints import Add, And, Eq, Mul, Ode, Real, RealVal
from stlmc.constraints.translation import polynomial_ode_solution, make_dynamics_consts
from stlmc.constraints.sympy_expression import SympyExpression
from stlmc.exceptions import NotSupportedError


class OdeTranslationTest(unittest.TestCase):
    def assertEquivalent(self, actual, expected):
        context = SympyExpression()
        self.assertEqual(sympy.expand(context.to_sympy(actual) -
                                      context.to_sympy(expected)), 0)

    def test_constant_acceleration_raw_and_instantiated(self):
        t = Real('elapsed')
        for suffix in ('', '_12_0_t'):
            x, v = Real('x' + suffix), Real('v' + suffix)
            initial_suffix = '_12_0' if suffix else ''
            x0, v0 = Real('x' + initial_suffix), Real('v' + initial_suffix)
            result = polynomial_ode_solution(Ode([x, v], [v0, RealVal('2')]), t,
                                             [x0, v0] if suffix else None)
            self.assertEquivalent(result[0], Add(x0, Add(Mul(v0, t), Mul(t, t))))
            self.assertEquivalent(result[1], Add(v0, Mul(RealVal('2'), t)))

    def test_dependency_order_and_parameter(self):
        x, v, a, t = map(Real, ('x', 'v', 'a', 'elapsed'))
        result = polynomial_ode_solution(Ode([x, v], [v, a]), t)
        context = SympyExpression()
        expression = context.to_sympy(result[0])
        self.assertEqual(sympy.diff(expression, context.symbol(t), 2), context.symbol(a))
        self.assertEquivalent(result[1], Add(v, Mul(a, t)))

    def test_endpoint_contains_acceleration_and_no_declaration_alias(self):
        x, v = Real('x_0_0_t'), Real('v_0_0_t')
        result = make_dynamics_consts(Ode([x, v], [Real('v_0_0'), RealVal('2')]))
        self.assertNotIn('_0_0_t', str(result))
        self.assertEquivalent(result.children[0].right,
                              Add(Real('x_0_0'), Add(Mul(Real('v_0_0'), Real('tau_1')),
                                                     Mul(Real('tau_1'), Real('tau_1')))))

    def test_unsupported_cycles_fail_not_euler(self):
        x, v, t = map(Real, ('x', 'v', 'elapsed'))
        for dynamics in (Ode([x], [x]), Ode([x, v], [v, x])):
            with self.assertRaises(NotSupportedError):
                polynomial_ode_solution(dynamics, t)

    def test_explicit_time_rejected(self):
        with self.assertRaises(NotSupportedError):
            polynomial_ode_solution(Ode([Real('x')], [Real('time')]), Real('elapsed'))

    def test_raw_identifier_suffix_is_not_encoder_metadata(self):
        # The current text grammar rejects underscores, but the typed AST
        # public helper must still preserve arbitrary caller-owned names.
        elapsed = Real('elapsed')
        result = polynomial_ode_solution(
            Ode([Real('position_0_t')], [RealVal('1')]), elapsed)
        self.assertEquivalent(result[0], Add(Real('position_0_t'), elapsed))

    def test_elapsed_collision_with_parameter_rejected(self):
        elapsed = Real('elapsed')
        with self.assertRaises(NotSupportedError):
            polynomial_ode_solution(Ode([Real('x')], [elapsed]), elapsed)

    def test_native_z3_rejects_euler_endpoint(self):
        import z3
        from stlmc.solver.z3 import z3Obj
        dynamics = Ode([Real('x_0_0_t'), Real('v_0_0_t')],
                       [Real('v_0_0'), RealVal('2')])
        fixed = [Eq(Real(name), RealVal(value)) for name, value in
                 [('x_0_0', '0'), ('v_0_0', '0'), ('tau_1', '1'),
                  ('x_0_t', '0'), ('v_0_t', '2')]]
        solver = z3.Solver()
        solver.add(z3Obj(And([make_dynamics_consts(dynamics)] + fixed)))
        self.assertEqual(solver.check(), z3.unsat)


if __name__ == '__main__':
    unittest.main()
