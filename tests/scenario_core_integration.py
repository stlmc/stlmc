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
from stlmc.solver.solver_factory import SolverFactory
from stlmc.exceptions import SolverUnavailableError
from stlmc.solver.abstract_solver import SolverStatus
from stlmc.algorithms.two_step import TwoStepAlgorithm
import stlmc.algorithms.two_step as two_step_module
original_matching = two_step_module.bounded_proposition_matching
expected_matching = None
def audited_matching(*args, **kwargs):
    global expected_matching
    expected_matching = original_matching(*args, **kwargs)
    return expected_matching
two_step_module.bounded_proposition_matching = audited_matching
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
core_class = SolverFactory().generate_formula_solver_factory(role='core')
scenario_class = SolverFactory().generate_formula_solver_factory()
original_core = core_class.unsat_core
expected_partition = None
expected_terminal = None
original_scenario_check = TwoStepAlgorithm.scenario_check
def capture_context(self, *args, **kwargs):
    global expected_partition, expected_terminal
    expected_partition, expected_terminal = args[10], args[8]
    return original_scenario_check(self, *args, **kwargs)
TwoStepAlgorithm.scenario_check = capture_context
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
    assert any(item is expected_terminal for item in self._assertions)
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
    for backend in ('z3', 'yices', 'cvc5'):
        try:
            replay = SolverFactory().generate_formula_solver_factory(backend)()
        except SolverUnavailableError:
            continue
        for item in self._assertions:
            replay.add(item)
        for tag in core:
            replay.add(self._tracked[tag])
        assert replay.check() is SolverStatus.UNSAT, backend
    count += 1
    return core
core_class.unsat_core = audited_core
original_add = scenario_class.add
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
scenario_class.add = audited_add
original_submit = Z3Solver.submit
def audited_submit(self, formula, *args, **kwargs):
    if self.config.get_section('common').get_value('two-step') != 'true':
        return original_submit(self, formula, *args, **kwargs)
    pending = [formula]
    retained = set()
    found_matching = False
    found_partition = False
    found_terminal = False
    while pending:
        item = pending.pop()
        if item is expected_matching:
            found_matching = True
        if item is expected_partition:
            found_partition = True
        if item is expected_terminal:
            found_terminal = True
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
    assert found_matching, 'refinement omitted shared complete proposition matching'
    assert found_partition, 'refinement omitted Psi_PAR'
    assert found_terminal, 'refinement omitted terminal definitions'
    if self.config.get_section('common').get_value('concrete') != 'true':
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
                 batch=1, two_step=True, bound=1, concrete=False,
                 scenario_backend='z3', core_backend='z3'):
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
 concrete = "%s"
}''' % (bound, str(two_step).lower(), path, str(preprocess).lower(), batch,
        str(concrete).lower()))
            env = dict(os.environ, PYTHONPATH=str(ROOT/'src'),
                       EQUIVALENT=str(int(equivalent)), PYTHONHASHSEED='0',
                       STLMC_SCENARIO_SOLVER=scenario_backend,
                       STLMC_CORE_SOLVER=core_backend)
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

    def test_concrete_refinement_retains_complete_matching(self):
        goal = '[][0,2] (x <= 1)'
        for equivalent in (False, True):
            reference, _ = self.run_case(goal, equivalent, two_step=False)
            for preprocess in (False, True):
                with self.subTest(equivalent=equivalent, preprocess=preprocess):
                    result, _ = self.run_case(goal, equivalent,
                                              preprocess=preprocess, concrete=True)
                    self.assertEqual(result, reference)

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

    def test_independent_backend_pairs_preserve_conditional_core_and_matching(self):
        sys.path.insert(0, str(ROOT/'src'))
        from stlmc.solver.solver_factory import SolverFactory
        from stlmc.exceptions import SolverUnavailableError
        available = []
        for backend in ('z3', 'yices', 'cvc5'):
            try:
                SolverFactory().generate_formula_solver_factory(backend)()
            except SolverUnavailableError:
                continue
            available.append(backend)
        for scenario, core in itertools.product(available, repeat=2):
            for goal, equivalent in (('[][0,2] (x <= 1)', False),
                                     ('(x < 3) U[0,1] (x >= 3)', True)):
                with self.subTest(scenario=scenario, core=core, goal=goal):
                    reference, _ = self.run_case(goal, equivalent, two_step=False)
                    result, verified = self.run_case(
                        goal, equivalent, preprocess=True, batch=2,
                        scenario_backend=scenario, core_backend=core)
                    self.assertEqual(result, reference)
                    self.assertGreater(verified, 0)


if __name__ == '__main__':
    unittest.main()
