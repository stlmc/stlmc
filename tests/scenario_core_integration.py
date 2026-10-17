"""Audit conditional cores and retained auxiliary values without dReal."""
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
RESULT = re.compile(r'status\s*:\s*(\w+)\s+(?:at|up to) bound\s+(\d+)')
MODEL = '''[0, 3] x;
{
 mode: true;
 inv: (and (x >= 0) (x <= 3));
 flow: d/dt[x] = 1;
 jump:
}
init: x = 0;
proposition:
goal: GOAL;
'''
WRAPPER = '''
import json, os, sys, re
from dataclasses import replace
from stlmc.application.options import RunOptions
from stlmc.constraints.constraints import And, Or, Not, Bool, BoolVal, Eq
from stlmc.solver.z3 import Z3FormulaSolver, Z3Solver
from stlmc.solver.abstract_solver import SolverStatus
from stlmc.algorithms.two_step import TwoStepAlgorithm
original_clear = TwoStepAlgorithm.clear
def audited_clear(self):
    result = original_clear(self)
    self.scenario_solver._audit_scenario = True
    return result
TwoStepAlgorithm.clear = audited_clear
original = RunOptions.from_configuration.__func__
RunOptions.from_configuration = classmethod(lambda cls, config: replace(
    original(cls, config),
    use_unary_bounded_temporal_form=os.environ['EQUIVALENT'] == '1'))
original_core = Z3FormulaSolver.unsat_core
count = 0
pending_auxiliary = []
expected_block = None
def conjuncts(formulas):
    pending = list(formulas)
    while pending:
        current = pending.pop()
        if isinstance(current, And):
            pending.extend(current.children)
        else:
            yield current
def audited_core(self):
    global count, expected_block
    core = original_core(self)
    auxiliary = set()
    # Only Boolean values, never full recurrences, are positive background.
    for item in conjuncts(self._assertions):
        if isinstance(item, Eq) and isinstance(item.left, Bool):
            name = item.left.id
            assert not name.startswith('chi^'), name
            if name.startswith(('rho^', 'parU^', 'parEnd')):
                assert isinstance(item.right, BoolVal), item
                auxiliary.add((name, item.right.value))
    for tag in core:
        literal = self._tracked[tag]
        if isinstance(literal, Eq) and isinstance(literal.left, Bool):
            assert not literal.left.id.startswith(('rho^', 'parU^', 'parEnd'))
    pending_auxiliary.append(auxiliary)
    expected_block = auxiliary
    replay = Z3FormulaSolver()
    for item in self._assertions:
        replay.add(item)
    for tag in core:
        replay.add(self._tracked[tag])
    assert replay.check() is SolverStatus.UNSAT
    count += 1
    return core
Z3FormulaSolver.unsat_core = audited_core
original_add = Z3FormulaSolver.add
def audited_add(self, formula):
    global expected_block
    if (getattr(self, '_audit_scenario', False)
            and isinstance(formula, Not) and expected_block is not None):
        values = set()
        for item in conjuncts([formula.child]):
            if (isinstance(item, Eq) and isinstance(item.left, Bool)
                    and isinstance(item.right, BoolVal)):
                values.add((item.left.id, item.right.value))
        assert expected_block <= values, expected_block - values
        expected_block = None
    return original_add(self, formula)
Z3FormulaSolver.add = audited_add
original_submit = Z3Solver.submit
def audited_submit(self, formula, *args, **kwargs):
    if self.config.get_section('common').get_value('two-step') != 'true':
        return original_submit(self, formula, *args, **kwargs)
    pending = [formula]
    retained = set()
    while pending:
        item = pending.pop()
        if isinstance(item, (And, Or)):
            pending.extend(item.children)
        elif (isinstance(item, Eq) and isinstance(item.left, Bool)
                and item.left.id.startswith(('rho^', 'parU^', 'parEnd'))):
            # Terminal and selected assignments are fine; full STL
            # recurrence equations must not be sent to refinement.
            if item.left.id.startswith('rho^'):
                assert isinstance(item.right, BoolVal), item
            if isinstance(item.right, BoolVal):
                retained.add((item.left.id, item.right.value))
    assert pending_auxiliary, 'refinement without audited core'
    for auxiliary in pending_auxiliary:
        assert auxiliary <= retained, auxiliary - retained
    pending_auxiliary.clear()
    return original_submit(self, formula, *args, **kwargs)
Z3Solver.submit = audited_submit
from stlmc.cli.mc import main
result = main()
print('CORE_AUDIT=' + json.dumps({'verified': count}))
sys.exit(result)
'''


class ScenarioCoreIntegrationTest(unittest.TestCase):
    def run_case(self, goal, equivalent, path='symbolic', preprocess=False,
                 batch=1, two_step=True, bound=1):
        with tempfile.TemporaryDirectory(prefix='stlmc-scenario-core-') as tmp:
            work = Path(tmp)
            model, config = work/'case.model', work/'case.cfg'
            model.write_text(MODEL.replace('GOAL', goal))
            config.write_text('''common {
 bound = %d
 time-bound = 2
 threshold = 0.01
 solver = "z3"
 two-step = "%s"
 parallel = "false"
 path-strategy = "%s"
 smt-preprocess = "%s"
 solver-batch-size = %d
}''' % (bound, str(two_step).lower(), path, str(preprocess).lower(), batch))
            env = dict(os.environ, PYTHONPATH=str(ROOT/'src'),
                       EQUIVALENT=str(int(equivalent)), PYTHONHASHSEED='0')
            result = subprocess.run(
                [sys.executable, '-c', WRAPPER, str(model), '-model-cfg', str(config)],
                cwd=work, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=30)
            self.assertEqual(result.returncode, 0, result.stdout)
            match = RESULT.search(result.stdout)
            self.assertIsNotNone(match, result.stdout)
            audit = re.search(r'CORE_AUDIT=(.*)', result.stdout)
            self.assertIsNotNone(audit, result.stdout)
            return (match[1], int(match[2])), json.loads(audit[1])['verified']

    def test_cores_match_one_step_across_options(self):
        for goal in ('[][0,2] (x <= 1)', '[][0,2] (x <= 3)'):
            for equivalent in (False, True):
                reference, _ = self.run_case(goal, equivalent, two_step=False)
                for path, preprocess, batch in itertools.product(
                        ('symbolic', 'explicit'), (False, True), (1, 2)):
                    with self.subTest(goal=goal, equivalent=equivalent,
                                      path=path, preprocess=preprocess, batch=batch):
                        result, _ = self.run_case(goal, equivalent,
                                                  path, preprocess, batch)
                        self.assertEqual(result, reference)

    def test_binary_formula_core_preserves_result(self):
        goal = '(x < 3) U[0,1] (x >= 3)'
        for equivalent in (False, True):
            with self.subTest(equivalent=equivalent):
                reference, _ = self.run_case(goal, equivalent, two_step=False)
                result, verified = self.run_case(goal, equivalent)
                self.assertEqual(result, reference)
                self.assertGreater(verified, 0)

    def test_predicate_crossing_requires_an_extra_partition_segment(self):
        # x(t)=t crosses the counterexample predicate x>1.01 in (0,2).
        # One unsplit flow segment cannot label that predicate consistently.
        for two_step in (False, True):
            with self.subTest(two_step=two_step):
                low, _ = self.run_case('[][0,2] (x <= 1)', False,
                                       two_step=two_step, bound=0)
                high, _ = self.run_case('[][0,2] (x <= 1)', False,
                                        two_step=two_step, bound=1)
                self.assertEqual(low, ('satisfied', 0))
                self.assertEqual(high, ('violated', 1))


if __name__ == '__main__':
    unittest.main()
