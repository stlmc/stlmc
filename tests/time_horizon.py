"""Backend-independent segment duration limits and refinement retention."""
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))

from stlmc.application.options import RunOptions
from stlmc.constraints.constraints import And, Eq, Real, RealVal
from stlmc.encoding.time import segment_duration_bounds
from stlmc.exceptions import IllegalArgumentError
from stlmc.parser.config_visitor import ConfigVisitor

MODEL = '''[0, 3] x;
{
 mode: true;
 inv: (and (x >= 0) (x <= 3));
 flow: x(t) = x(0) + t;
 jump: true => (x' = x);
}
init: x = 0;
proposition:
goal: GOAL;
'''

AUDIT = '''
import json, sys
from stlmc.cli.mc import main
from stlmc.algorithms.two_step import TwoStepAlgorithm
import stlmc.algorithms.two_step as module
from stlmc.constraints.constraints import And
from stlmc.solver.z3 import Z3FormulaSolver
from stlmc.solver.abstract_solver import SolverStatus
expected = None
audits = {'batches': 0, 'cores_without_horizon_tracks': 0}
original_context = TwoStepAlgorithm.scenario_check
def context(self, *args, **kwargs):
    global expected
    expected = kwargs['duration_const']
    return original_context(self, *args, **kwargs)
TwoStepAlgorithm.scenario_check = context
original_core = Z3FormulaSolver.unsat_core
def core(self):
    result = original_core(self)
    horizon = {repr(item) for item in expected.children}
    reduced = {tag for tag in result if repr(self._tracked[tag]) not in horizon}
    replay = Z3FormulaSolver()
    for item in self._assertions:
        replay.add(item)
    for tag in reduced:
        replay.add(self._tracked[tag])
    if replay.check() is SolverStatus.UNSAT:
        result = reduced
    if not any(repr(self._tracked[tag]) in horizon for tag in result):
        audits['cores_without_horizon_tracks'] += 1
    return result
Z3FormulaSolver.unsat_core = core
original_batch = module.partitioned_candidate_batch_formula
def batch(candidates, partition):
    for common, scenario in candidates:
        assert isinstance(common, And)
        # H is shared, not conditional on whatever literals the core retained.
        assert any(repr(child) == repr(expected) for child in common.children)
        audits['batches'] += 1
    return original_batch(candidates, partition)
module.partitioned_candidate_batch_formula = batch
code = main()
print('HORIZON_AUDIT=' + json.dumps(audits))
sys.exit(code)
'''


class SegmentDurationTest(unittest.TestCase):
    def test_one_pair_per_segment_and_no_input_mutation(self):
        limits = segment_duration_bounds(2, 1.25)
        self.assertEqual(len(limits.children), 6)
        self.assertEqual(repr(limits.children[1].right), '1.25')
        self.assertEqual(repr(limits.children[-1].left.left), 'tau_3')
        self.assertEqual(repr(limits.children[-1].left.right), 'tau_2')
        self.assertEqual(repr(segment_duration_bounds(0, 0).children[1].right), '0.0')

    def test_invalid_horizons_and_bounds_are_rejected(self):
        for horizon in (-1, float('inf'), float('-inf'), float('nan')):
            with self.subTest(horizon=horizon), self.assertRaisesRegex(ValueError, 'time-horizon'):
                segment_duration_bounds(0, horizon)
        with self.assertRaises(ValueError):
            segment_duration_bounds(-1, 1)

    def test_option_alias_and_finite_validation(self):
        config = ConfigVisitor().parse_from_file(str(ROOT / 'src/stlmc/default.cfg'))
        common = config.get_section('common')
        common.arguments.update({'bound': '1', 'time-bound': '2'})
        self.assertEqual(RunOptions.from_configuration(config).time_horizon, 2)
        for value in ('nan', 'inf', '-1', 'not-a-number'):
            common.set_value('time-horizon', value)
            with self.subTest(value=value), self.assertRaisesRegex(IllegalArgumentError, 'time-horizon'):
                RunOptions.from_configuration(config)
        common.set_value('time-horizon', '0')
        self.assertEqual(RunOptions.from_configuration(config).time_horizon, 0)

    def test_native_formula_respects_zero_exact_boundary_and_overflow(self):
        try:
            from stlmc.solver.z3 import Z3FormulaSolver
        except ImportError as error:
            self.skipTest(str(error))
        from stlmc.solver.abstract_solver import SolverStatus
        for times, expected in (((0, 0, 1), True), ((0, 1, 2), True),
                                ((0, 1.01, 2), False), ((0, -0.01, 0), False)):
            solver = Z3FormulaSolver()
            solver.add(segment_duration_bounds(1, 1))
            for index, value in enumerate(times):
                solver.add(Eq(Real('tau_{}'.format(index)), RealVal(str(value))))
            self.assertEqual(solver.check() is SolverStatus.SAT, expected)

    def test_dreal_keeps_native_limit_and_shared_tau_limit(self):
        from stlmc.constraints.constraints import Integral, Ode
        from stlmc.solver.dreal import dRealSolver, drealObj
        limits = segment_duration_bounds(0, 1)
        flow = Integral(0, [Real('x_0_t')], [Real('x_0_0')],
                        Ode([Real('x_0_0')], [RealVal('1')]))
        formula = And([flow, limits])
        declarations, bound = dRealSolver().get_declared_variables(formula, 1, 2)
        self.assertEqual(bound, 0)
        self.assertIn('(declare-fun time_0 () Real [0, 1])', declarations)
        text = drealObj(formula)
        self.assertIn('(<= (- tau_1 tau_0) 1.0)', text)
        self.assertIn('(>= (- tau_1 tau_0) 0)', text)


class TimeHorizonIntegrationTest(unittest.TestCase):
    def run_case(self, backend, two_step, reach=False, path='symbolic',
                 horizon=1, bound=1, audit=False, preprocess=False):
        if importlib.util.find_spec(backend) is None:
            self.skipTest('{} binding is optional'.format(backend))
        if importlib.util.find_spec('z3') is None:
            self.skipTest('default internal Z3 is optional')
        temp_root = ROOT / '.tmp'
        temp_root.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='horizon-', dir=temp_root) as directory:
            work = Path(directory)
            goal = 'reach (x >= 1.5)' if reach else '[][0,2] (x <= -1)'
            (work / 'case.model').write_text(MODEL.replace('GOAL', goal))
            (work / 'case.cfg').write_text('''common {
 bound = %d
 time-bound = 2
 time-horizon = %s
 threshold = 0
 solver = "%s"
 two-step = "%s"
 parallel = "false"
 path-strategy = "%s"
 smt-preprocess = "%s"
 solver-batch-size = 2
}''' % (bound, horizon, backend, str(two_step).lower(), path, str(preprocess).lower()))
            wrapper = AUDIT if audit else 'from stlmc.cli.mc import main; raise SystemExit(main())'
            environment = dict(os.environ, PYTHONPATH=str(ROOT / 'src'),
                               STLMC_DISABLE_UPDATE_CHECK='1', OPENBLAS_NUM_THREADS='1',
                               STLMC_SCENARIO_SOLVER='z3', STLMC_CORE_SOLVER='z3')
            result = subprocess.run([sys.executable, '-c', wrapper, str(work / 'case.model'),
                                     '-model-cfg', str(work / 'case.cfg')],
                                    cwd=work, env=environment, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
            if result.returncode == 3 and 'unavailable' in result.stdout.lower():
                self.skipTest('optional native backend unavailable: ' + result.stdout[-1000:])
            self.assertEqual(result.returncode, 0, result.stdout)
            match = re.search(r'status\s*:\s*(\w+)\s+(?:at|up to) bound\s+(\d+)', result.stdout)
            self.assertIsNotNone(match, result.stdout)
            if audit:
                details = json.loads(re.search(r'HORIZON_AUDIT=(.*)', result.stdout)[1])
                self.assertGreater(details['batches'], 0)
                if not preprocess and horizon == 2:
                    self.assertGreater(details['cores_without_horizon_tracks'], 0)
            return match[1], int(match[2])

    def test_all_algebraic_backends_both_engines_paths_and_goal_kinds(self):
        for backend in ('z3', 'yices', 'cvc5'):
            for two_step in (False, True):
                for path in ('symbolic', 'explicit'):
                    for reach in (False, True):
                        with self.subTest(backend=backend, two_step=two_step, path=path, reach=reach):
                            self.assertEqual(self.run_case(backend, two_step, reach, path),
                                             ('reachable' if reach else 'violated', 1))

    def test_bound_zero_is_excluded_only_by_horizon(self):
        for backend in ('z3', 'yices', 'cvc5'):
            for two_step in (False, True):
                with self.subTest(backend=backend, two_step=two_step):
                    self.assertEqual(self.run_case(backend, two_step, bound=0), ('satisfied', 0))
                    self.assertEqual(self.run_case(backend, two_step, bound=0, horizon=2), ('violated', 0))

    def test_shared_horizon_remains_when_conditional_core_omits_it(self):
        self.assertEqual(self.run_case('z3', True, horizon=2, audit=True), ('violated', 0))
        for reach in (False, True):
            for preprocess in (False, True):
                with self.subTest(reach=reach, preprocess=preprocess):
                    self.assertEqual(self.run_case('z3', True, reach=reach, audit=True, preprocess=preprocess),
                                     ('reachable' if reach else 'violated', 1))

    def test_zero_horizon_is_a_valid_bounded_query_not_a_usage_error(self):
        for two_step in (False, True):
            with self.subTest(two_step=two_step):
                self.assertEqual(self.run_case('z3', two_step, horizon=0, bound=0), ('satisfied', 0))


if __name__ == '__main__':
    unittest.main()
