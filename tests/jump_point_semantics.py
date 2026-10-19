"""A jump's singleton observes the post-reset state, not the flow left limit."""

import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest

import z3

from stlmc.algorithms.shared_stl import bounded_proposition_matching
from stlmc.artifacts.codec import load_artifact
from stlmc.constraints.analysis import get_vars
from stlmc.constraints.substitution import substitution
from stlmc.constraints.constraints import (
    And, Bool, FinallyFormula, Geq, Gt, Int, Integral, Interval, Leq, Lt,
    Ode, Real, RealVal, universeInterval,
)
from stlmc.encoding.model_linking import contradiction_gen, path2const
from stlmc.encoding.symbolic_discrete import chi
from stlmc.exceptions import NotSupportedError
from stlmc.solver.z3 import z3Obj
from stlmc.visualize.robustness import robustness
from stlmc.visualize.sampling import get_sub_time_samples
from stlmc.visualize.visualizer import Visualizer


class PostJumpEncodingTest(unittest.TestCase):
    def test_closed_window_counterexample_at_an_exact_forced_reset(self):
        source = """int location;
[0, 10] x; [0, 3] clock;
{ mode: location = 0; inv: clock <= 1;
  flow: d/dt[x] = 0; d/dt[clock] = 1;
  jump: clock = 1 => (and (location' = 1) (x' = 0) (clock' = clock)); }
{ mode: location = 1; inv: true;
  flow: d/dt[x] = 1; d/dt[clock] = 1;
  jump: }
init: location = 0; x = 5; clock = 0;
proposition:
goal: [safety]: [][0, 1] (x >= 1);
"""
        root = Path(__file__).resolve().parent.parent
        environment = dict(os.environ, PYTHONPATH=str(root / 'src'),
                           STLMC_DISABLE_UPDATE_CHECK='1', OPENBLAS_NUM_THREADS='1')
        with tempfile.TemporaryDirectory() as directory:
            working = Path(directory)
            (working / 'reset.model').write_text(source)
            completed = subprocess.run([
                sys.executable, '-c',
                'from stlmc.cli.mc import main; raise SystemExit(main())',
                'reset.model', '-goal', 'safety', '-bound', '1',
                '-time-bound', '2', '-threshold', '0', '-solver', 'z3', '-visualize',
            ], cwd=working, env=environment, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=30)
            self.assertEqual(completed.returncode, 0, completed.stdout)
            self.assertRegex(completed.stdout, r'status\s*:\s*violated at bound 1')
            artifact = next(working.glob('*.counterexample'))
            data = load_artifact(artifact)
            self.assertEqual(float(data[0][Real('tau_1')].value), 1.)
            self.assertEqual(float(data[0][Real('x_0_t')].value), 5.)
            self.assertEqual(float(data[0][Real('x_1_0')].value), 0.)
            _, values, *_ = Visualizer().generate_data(*data[:9])
            expanded = substitution(data[6], data[5])
            self.assertEqual(values[expanded][0][0], -1.)

    def model(self):
        flows = {}
        for bound in range(2):
            start, end = Real('x_{}_0'.format(bound)), Real('x_{}_t'.format(bound))
            flows[Bool('newIntegral_0_{}'.format(bound))] = Integral(
                0, [end], [start], Ode([start], [RealVal('0')]))
        return SimpleNamespace(mode_var_dict={'location': Int('location')},
                               modules=[{}], boolean_abstract=flows)

    def test_point_matching_and_learning_use_post_reset_and_post_mode(self):
        atom = Lt(Real('x') + Int('location'), RealVal('3'))
        flag = chi(3, 3, atom)
        matching = path2const({(3, flag): atom}, self.model())
        learned = And(list(contradiction_gen({flag}, {atom}, self.model())))
        for formula in (matching, learned):
            with self.subTest(formula=formula):
                self.assertIn(Real('x_1_0'), get_vars(formula))
                self.assertIn(Int('location_1'), get_vars(formula))
                self.assertNotIn(Real('x_0_t'), get_vars(formula))
                for truth in (True, False):
                    solver = z3.Solver()
                    solver.add(z3Obj(formula), z3.Real('x_0_t') == 5,
                               z3.Real('x_1_0') == 0, z3.Int('location_0') == 0,
                               z3.Int('location_1') == 1, z3.Bool(flag.id) == truth)
                    self.assertEqual(solver.check(), z3.sat if truth else z3.unsat)

    def test_interval_closure_keeps_pre_reset_endpoint(self):
        atom = Gt(Real('x'), RealVal('2'))
        flag = chi(2, 2, atom)
        intervals, points = contradiction_gen({flag}, {atom}, self.model())
        self.assertIn(Real('x_0_t'), get_vars(intervals))
        self.assertNotIn(Real('x_1_0'), get_vars(intervals))
        for endpoint, expected in ((5, z3.sat), (0, z3.unsat)):
            solver = z3.Solver()
            solver.add(z3Obj(And([intervals, points])), z3.Bool(flag.id),
                       z3.Real('x_0_0') == 5, z3.Real('x_0_t') == endpoint,
                       z3.Real('x_1_0') == 0, z3.Real('tau_0') == 0,
                       z3.Real('tau_1') == 1)
            self.assertEqual(solver.check(), expected)

    def test_repeated_time_does_not_replace_a_point_with_an_empty_flow(self):
        atom = Gt(Real('x'), RealVal('2'))
        flow_flag, point_flag = chi(2, 2, atom), chi(3, 3, atom)
        intervals, points = contradiction_gen({flow_flag, point_flag}, {atom}, self.model())
        solver = z3.Solver()
        solver.add(z3Obj(And([intervals, points])), z3.Bool(flow_flag.id),
                   z3.Not(z3.Bool(point_flag.id)), z3.Real('x_0_0') == 0,
                   z3.Real('x_0_t') == 5, z3.Real('x_1_0') == 0,
                   z3.Real('tau_0') == 0, z3.Real('tau_1') == 0)
        self.assertEqual(solver.check(), z3.sat)

    def test_initial_point_and_half_open_terminal_state(self):
        atom = Gt(Real('x'), RealVal('2'))
        first = chi(1, 1, atom)
        point = path2const({(1, first): atom}, self.model())
        self.assertIn(Real('x_0_0'), get_vars(point))
        self.assertNotIn(Real('x_0_t'), get_vars(point))
        complete = bounded_proposition_matching(self.model(), {atom}, 4)
        # J1={tau0}, J2=(tau0,tau1), J3={tau1}, J4=(tau1,tau2).
        # There is no singleton at the excluded terminal tau2.
        self.assertNotIn(Real('x_2_0'), get_vars(complete))


class PostJumpSamplingTest(unittest.TestCase):
    def setUp(self):
        self.x, self.mode, self.enabled = Real('x'), Int('location'), Bool('enabled')
        self.times = [[0., .5, 1.], [1., 1.5, 2.]]
        self.points = {self.x: [[5., 5., 5.], [0., 0., 0.]]}
        self.discrete = {self.mode: [[0., 0., 0.], [1., 1., 1.]],
                         self.enabled: [[-1., -1., -1.], [1., 1., 1.]]}

    def evaluate(self, formula, time, cache=None):
        return robustness(formula, self.points, self.discrete, time,
                          self.times, 2., {} if cache is None else cache)

    def test_all_comparisons_observe_post_reset_at_shared_time(self):
        for operator, expected in ((Geq, -2.), (Gt, -2.), (Leq, 2.), (Lt, 2.)):
            with self.subTest(operator=operator.__name__):
                self.assertEqual(self.evaluate(operator(self.x, RealVal('2')), 1.), expected)

    def test_mode_boolean_and_mixed_predicate_observe_the_same_post_state(self):
        self.assertEqual(self.evaluate(self.enabled, 1.), math.inf)
        self.assertEqual(self.evaluate(Lt(self.mode, RealVal('.5')), 1.), -.5)
        self.assertEqual(self.evaluate(Lt(self.x + self.mode, RealVal('3')), 1.), 2.)

    def test_before_and_after_boundary_and_cache_order_are_unchanged(self):
        atom = Gt(self.x, RealVal('2'))
        for order in ((.5, 1., 1.5), (1.5, 1., .5)):
            cache = {}
            result = {time: self.evaluate(atom, time, cache) for time in order}
            self.assertEqual(result, {.5: 3., 1.: -2., 1.5: -2.})
        self.assertEqual(self.evaluate(self.enabled, .5), -math.inf)
        self.assertEqual(self.evaluate(self.enabled, 1.5), math.inf)

    def test_zero_duration_segments_choose_the_last_post_state(self):
        times = [[0., 1.], [1., 1.], [1., 2.]]
        points = {self.x: [[5., 5.], [99., 99.], [0., 0.]]}
        discrete = {self.enabled: [[-1., -1.], [1., 1.], [-1., -1.]]}
        self.assertEqual(robustness(Lt(self.x, RealVal('2')), points, discrete,
                                    1., times, 2., {}), 2.)
        self.assertEqual(robustness(self.enabled, points, discrete,
                                    1., times, 2., {}), -math.inf)

    def test_terminal_sample_is_display_only_not_a_temporal_witness(self):
        self.assertEqual(self.evaluate(Lt(self.x, RealVal('2')), 2.), 2.)
        self.assertEqual(get_sub_time_samples(self.times, 2., 2., 2.), [])
        terminal = FinallyFormula(Interval(True, RealVal('2'), True, RealVal('2')),
                                  universeInterval, Lt(self.x, RealVal('2')))
        self.assertEqual(self.evaluate(terminal, 0.), -math.inf)

    def test_missing_times_are_not_interpolated_or_extrapolated(self):
        for time in (-.1, .25, 2.1):
            with self.subTest(time=time), self.assertRaises(NotSupportedError):
                self.evaluate(Gt(self.x, RealVal('2')), time)


if __name__ == '__main__':
    unittest.main()
