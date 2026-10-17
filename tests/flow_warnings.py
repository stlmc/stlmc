from pathlib import Path
import tempfile
import unittest
import warnings

from stlmc.parser.flow_warnings import ClosedFormFlowWarning, InvalidSolutionFlowError
from stlmc.parser.model_visitor import ModelVisitor


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

    def test_battery_fixture_is_rejected_without_changing_model(self):
        path = Path(__file__).resolve().parent/'benchmarks/bat-poly/bat.model'
        before = path.read_bytes()
        with self.assertRaisesRegex(InvalidSolutionFlowError, 'bat.model:32:'):
            ModelVisitor().get_parse_tree(str(path))
        self.assertEqual(path.read_bytes(), before)

    def test_state_dependent_initial_difference_remains_advisory(self):
        # x(t)=t can be valid under x(0)=0, so a blanket error is unsound.
        _, captured = self.parse('[0,10] x;', 'x(t)=t;')
        self.assertEqual(len(captured), 1)
        self.assertIn('state-dependent', str(captured[0].message))


if __name__ == '__main__':
    unittest.main()
