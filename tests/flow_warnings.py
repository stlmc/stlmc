from pathlib import Path
from fractions import Fraction
import tempfile
import unittest
import warnings

from stlmc.parser.flow_warnings import ClosedFormFlowWarning, InvalidSolutionFlowError
from stlmc.parser.model_visitor import ModelVisitor
from stlmc.constraints.constraints import (
    Add, Constant, Div, Eq, Function, Mul, Neg, Ode, Pow, Real, RealVal,
    Sub, Variable,
)


def exact_value(expression, values):
    """Small independent rational evaluator for polynomial test identities."""
    if isinstance(expression, Constant):
        return Fraction(expression.value)
    if isinstance(expression, Variable):
        return values[expression.id]
    if isinstance(expression, Neg):
        return -exact_value(expression.child, values)
    left = exact_value(expression.left, values)
    right = exact_value(expression.right, values)
    operations = {Add: lambda: left + right, Sub: lambda: left - right,
                  Mul: lambda: left * right, Div: lambda: left / right,
                  Pow: lambda: left ** int(right)}
    return operations[type(expression)]()


def walk(expression):
    yield expression
    for child in getattr(expression, 'children', ()):
        yield from walk(child)


class FlowWarningTest(unittest.TestCase):
    def parse(self, declarations, flow):
        source = '{}\n{{mode: true; inv: flow: {} jump:}}\ninit: true;\ngoal: true;\n'.format(
            declarations, flow)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'flow.model'
            path.write_text(source)
            with warnings.catch_warnings(record=True) as captured:
                warnings.simplefilter('always', ClosedFormFlowWarning)
                model = ModelVisitor().get_parse_tree(str(path))[0]
            return model, captured

    def test_initial_offset_is_reported_with_source_location(self):
        with self.assertRaises(InvalidSolutionFlowError) as raised:
            self.parse('[0,10] x;', 'x(t)=0.1*(1-2*t+2*t*t)+0.5+x(0);')
        message = str(raised.exception)
        self.assertIn('FLOW_INITIAL_VALUE', message)
        self.assertIn('3/5', message)
        self.assertIn('flow.model:2:', message)
        self.assertIn('verification was not started', message)

    def test_zero_initial_offset_does_not_imply_subdivision_safe(self):
        _, captured = self.parse('[0,10] x;', 'x(t)=x(0)+t*t;')
        self.assertEqual(len(captured), 1)
        self.assertIn('FLOW_SUBDIVISION', str(captured[0].message))

    def test_valid_coupled_ball_flow_is_not_flagged(self):
        _, captured = self.parse('[-50,50] x; [-50,50] v;',
            'x(t)=x(0)+v(0)*t-0.5*t*t; v(t)=v(0)-t;')
        self.assertEqual(captured, [])

    def test_linear_and_symbolic_cancellation_are_not_flagged(self):
        _, captured = self.parse('[0,10] x;',
            'x(t)=x(0)+t+t*t-t*t;')
        self.assertEqual(captured, [])

    def test_ode_and_unsupported_functions_are_not_rejected(self):
        _, ode = self.parse('[0,10] x;', 'd/dt[x]=x;')
        _, unsupported = self.parse('[0,10] x;', 'x(t)=x(0)+sin(t);')
        self.assertEqual(ode, [])
        self.assertEqual(unsupported, [])

    def test_unsupported_component_does_not_hide_known_offset(self):
        with self.assertRaisesRegex(InvalidSolutionFlowError, 'FLOW_INITIAL_VALUE'):
            self.parse('[0,10] x; [0,10] y;', 'x(t)=x(0)+1; y(t)=y(0)+sin(t);')

    def battery_fixture(self, scope='bat-poly'):
        path = Path(__file__).resolve().parent/'benchmarks'/scope/'bat.model'
        before = path.read_bytes()
        with warnings.catch_warnings(record=True) as captured:
            warnings.simplefilter('always', ClosedFormFlowWarning)
            model = ModelVisitor().get_parse_tree(str(path))[0]
        self.assertEqual(captured, [])
        self.assertEqual(path.read_bytes(), before)
        return model

    def test_battery_fixture_has_valid_clock_augmented_flows(self):
        model = self.battery_fixture()
        self.assertIn(Real('a'), model.range_dict)
        self.assertIn(Eq(Real('a'), RealVal('0')), list(walk(model.init)))
        initial = {'a': Fraction(7, 3), 'd1': Fraction(-2, 3),
                   'd2': Fraction(1, 7), 'g1': Fraction(8), 'g2': Fraction(7)}
        for index, module in enumerate(model.modules):
            dynamics = module['flow']
            if isinstance(dynamics, Ode):
                self.assertEqual(index, len(model.modules) - 1)
                expressions = dict(zip(dynamics.vars, dynamics.exps))
                self.assertEqual(exact_value(expressions[Real('a')], initial), 1)
                for variable in ('d1', 'd2', 'g1', 'g2'):
                    self.assertEqual(exact_value(expressions[Real(variable)], initial), 0)
                continue
            self.assertIsInstance(dynamics, Function)
            def advance(state, duration):
                values = dict(state, time=duration)
                return {v.id: exact_value(e, values)
                        for v, e in zip(dynamics.vars, dynamics.exps)}
            with self.subTest(mode=index):
                self.assertEqual(advance(initial, Fraction(0)), initial)
                for first, second in ((Fraction(1, 3), Fraction(2, 5)),
                                      (Fraction(3, 2), Fraction(7, 4))):
                    self.assertEqual(advance(initial, first + second),
                                     advance(advance(initial, first), second))

    def test_cubic_clock_flow_exact_initial_value_and_restart_identity(self):
        integral = ('0.1*t-0.2*a(0)*t-0.1*t*t+0.2*a(0)*a(0)*t'
                    '+0.2*a(0)*t*t+(1/15)*t*t*t')
        for sign in ('+', '-'):
            model, captured = self.parse('[0,25] a; [-30,30] d;',
                'a(t)=a(0)+t; d(t)=d(0){}({});'.format(sign, integral))
            self.assertEqual(captured, [])
            dynamics = model.modules[0]['flow']
            start = {'a': Fraction(7, 3), 'd': Fraction(2, 7)}
            def advance(state, duration):
                values = dict(state, time=duration)
                return {v.id: exact_value(e, values)
                        for v, e in zip(dynamics.vars, dynamics.exps)}
            with self.subTest(sign=sign):
                self.assertEqual(advance(start, Fraction(0)), start)
                first, second = Fraction(2, 3), Fraction(5, 4)
                self.assertEqual(advance(start, first + second),
                                 advance(advance(start, first), second))

    def test_battery_fixture_integrates_the_intended_rates_exactly(self):
        model = self.battery_fixture()
        start = {'a': Fraction(2, 3), 'd1': Fraction(3, 7),
                 'd2': Fraction(5, 7), 'g1': Fraction(8), 'g2': Fraction(7)}
        # (integrated polynomial sign, additional constant rate), by mode.
        rates = (((1, Fraction(1, 2)), (1, Fraction(1, 2))),
                 ((1, 1), (-1, 0)), ((-1, 0), (1, 1)),
                 ((0, 0), (1, 1)), ((1, 1), (0, 0)))
        for index, module in enumerate(model.modules[:-1]):
            expressions = dict(zip(module['flow'].vars, module['flow'].exps))
            for time in (Fraction(1, 3), Fraction(2, 3), Fraction(1), Fraction(4, 3)):
                age = start['a']
                integral = (time/Fraction(10) - age*time/Fraction(5)
                            - time*time/Fraction(10) + age*age*time/Fraction(5)
                            + age*time*time/Fraction(5) + time**3/Fraction(15))
                for name, (sign, extra) in zip(('d1', 'd2'), rates[index]):
                    with self.subTest(mode=index, time=time, variable=name):
                        self.assertEqual(exact_value(expressions[Real(name)], dict(start, time=time)),
                                         start[name] + sign*integral + extra*time)

    def test_battery_cubic_rates_and_restart_identity_with_independent_sympy(self):
        import sympy as sp

        def symbolic(expression):
            if isinstance(expression, Constant):
                return sp.Rational(expression.value)
            if isinstance(expression, Variable):
                return sp.Symbol(expression.id)
            if isinstance(expression, Neg):
                return -symbolic(expression.child)
            left, right = symbolic(expression.left), symbolic(expression.right)
            return {Add: lambda: left+right, Sub: lambda: left-right,
                    Mul: lambda: left*right, Div: lambda: left/right,
                    Pow: lambda: left**right}[type(expression)]()

        time, split, age = sp.symbols('time split a')
        polynomial_rate = (1-2*(age+time)+2*(age+time)**2)/sp.Integer(10)
        rates = (((1, sp.Rational(1, 2)), (1, sp.Rational(1, 2))),
                 ((1, 1), (-1, 0)), ((-1, 0), (1, 1)),
                 ((0, 0), (1, 1)), ((1, 1), (0, 0)), ((0, 0), (0, 0)))
        for scope in ('bat-poly', 'bat-poly-small'):
            model = self.battery_fixture(scope)
            for index, module in enumerate(model.modules):
                dynamics = module['flow']
                self.assertIsInstance(dynamics, Function)
                expressions = {sp.Symbol(v.id): symbolic(e)
                               for v, e in zip(dynamics.vars, dynamics.exps)}
                self.assertEqual(sp.expand(expressions[age] - age - time), 0)
                for variable, expression in expressions.items():
                    with self.subTest(scope=scope, mode=index, variable=variable):
                        self.assertEqual(sp.expand(expression.subs(time, 0)-variable), 0)
                        # Replace elapsed time and every initial state together:
                        # F(split, F(time,x)), not sequential substitutions.
                        restarted = expression.xreplace({**expressions, time: split})
                        self.assertEqual(sp.expand(expression.subs(time, time+split)-restarted), 0)
                for name, (sign, load) in zip(('d1', 'd2'), rates[index]):
                    with self.subTest(scope=scope, mode=index, rate=name):
                        self.assertEqual(sp.expand(sp.diff(expressions[sp.Symbol(name)], time)
                                                   - sign*polynomial_rate - load), 0)

    def test_battery_real_jumps_reset_clock_but_stl_splits_preserve_it(self):
        for scope in ('bat-poly', 'bat-poly-small'):
            with self.subTest(scope=scope):
                self.check_battery_clock_transitions(self.battery_fixture(scope))

    def check_battery_clock_transitions(self, model):
        model.gen_stl_condition()
        _, tracks = model.make_jump_consts(0)
        for index, module in enumerate(model.modules):
            declared = len(module['jump'])
            for reset in module['jump'].values():
                self.assertIn(Eq(Real('a' + model.next_str), RealVal('0')),
                              list(walk(reset)))
            prefix = 'm_{}@jump^'.format(index)
            module_tracks = [(label, encoded) for label, encoded in tracks.items()
                             if label.id.startswith(prefix)]
            self.assertEqual(len(module_tracks), declared+1)
            for label, encoded in module_tracks:
                jump_index = int(label.id[len(prefix):].split('_')[0])
                expected = Eq(Real('a_1_0'),
                              Real('a_0_t') if jump_index == declared else RealVal('0'))
                self.assertIn(expected, list(walk(encoded)))

    def test_state_dependent_initial_difference_remains_advisory(self):
        # x(t)=t can be valid under x(0)=0, so a blanket error is unsound.
        _, captured = self.parse('[0,10] x;', 'x(t)=t;')
        self.assertEqual(len(captured), 1)
        self.assertIn('state-dependent', str(captured[0].message))


if __name__ == '__main__':
    unittest.main()
