"""Browser form values override configuration without changing model goals."""
import importlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))


class UiConfigurationTest(unittest.TestCase):
    def setUp(self):
        try:
            self.api = importlib.import_module('stlmc.ui.app')
        except ImportError as error:
            self.skipTest('Optional UI dependencies are unavailable: ' + str(error))

    def configuration(self, text):
        from stlmc.parser.config_visitor import ConfigVisitor
        visitor = ConfigVisitor()
        config = visitor.parse_from_file(str(ROOT / 'src/stlmc/default.cfg'))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'input.cfg'; path.write_text(text)
            return visitor.parse_from_file(str(path), config)

    def test_form_values_override_false_and_empty_without_losing_inheritance(self):
        original = '''common { goal="f1" two-step="true" reach="true"
solver="dreal" bound=99 time-bound=400 threshold=9 path-strategy="explicit"
parallel="true" time-horizon=3 }
z3 { logic="QF_LRA" }
yices extends z3 {}
dreal { precision=0.000001 ode-order=10 }
'''
        request = self.api.RunRequest(model='not executed', config=original,
            solver='z3', bound=2, time_bound=5, threshold=0, goal='',
            path_strategy='symbolic', two_step=False, reach=False)
        text = self.api.effective_config(request)
        self.assertTrue(text.startswith(original))
        config = self.configuration(text)
        common = config.get_section('common')
        for key, expected in {'goal': 'all', 'two-step': 'false', 'reach': 'false',
                'solver': 'z3', 'bound': '2', 'time-bound': '5.0', 'threshold': '0.0',
                'path-strategy': 'symbolic', 'visualize': 'false',
                'parallel': 'true', 'time-horizon': '3'}.items():
            self.assertEqual(common.get_value(key), expected, key)
        self.assertEqual(config.get_section('yices').get_value('logic'), 'QF_LRA')
        self.assertEqual(config.get_section('dreal').get_value('precision'), '0.000001')
        self.assertEqual(config.get_section('dreal').get_value('ode-order'), '10')

    def test_checked_flags_and_named_goal_override_false_config(self):
        request = self.api.RunRequest(model='not executed',
            config='common { goal="f1" two-step="false" reach="false" }',
            goal='target', two_step=True, reach=True)
        common = self.configuration(self.api.effective_config(request)).get_section('common')
        self.assertEqual(common.get_value('goal'), 'target')
        self.assertEqual(common.get_value('two-step'), 'true')
        self.assertEqual(common.get_value('reach'), 'true')

    def test_default_solver_preserves_config_or_uses_auto_when_omitted(self):
        for text, expected in [('', 'auto'), ('common {solver="dreal"}', 'dreal')]:
            request = self.api.RunRequest(model='not executed', config=text)
            self.assertIsNone(request.solver)
            common = self.configuration(self.api.effective_config(request)).get_section('common')
            self.assertEqual(common.get_value('solver'), expected)
        request = self.api.RunRequest(model='not executed',
            config='common {solver="dreal"}', solver='auto')
        common = self.configuration(self.api.effective_config(request)).get_section('common')
        self.assertEqual(common.get_value('solver'), 'auto')

    def test_unedited_form_is_not_a_configuration_layer(self):
        original = 'common {bound=7 time-bound=8 two-step="true" goal="f2"}'
        request = self.api.RunRequest(model='not executed', config=original)
        self.assertEqual(self.api.effective_config(request), original)
        for key in ('solver', 'bound', 'time_bound', 'threshold', 'goal', 'two_step', 'reach'):
            self.assertIsNone(getattr(request, key))

    def test_start_passes_effective_config_through_the_real_cli_merge(self):
        from stlmc.cli.command import CliCommand
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch.object(self.api, 'RUNS', Path(directory)), \
                mock.patch.object(self.api, 'JOBS', {}), \
                mock.patch.object(self.api, 'ACTIVE', None), \
                mock.patch.object(self.api, 'health', return_value={'stlmc': True}), \
                mock.patch.object(self.api.threading, 'Thread'), \
                mock.patch('stlmc.cli.parser.banner', return_value='STLmc test'), \
                mock.patch.object(self.api.subprocess, 'Popen', return_value=SimpleNamespace(pid=123)) as spawn:
            request = self.api.RunRequest(model='not parsed by the mocked worker',
                config='common {goal="f1" two-step="true" reach="true"}',
                goal='', two_step=False, reach=False, bound=0, time_bound=1, threshold=0)
            job = self.api.start(request)
            try:
                command = spawn.call_args.args[0]
                self.assertEqual(command[:4], [sys.executable, '-u', '-m', 'stlmc.ui.worker'])
                arguments = list(command[4:])
                working = Path(directory) / job['id']
                arguments[0] = str(working / 'input.model')
                arguments[arguments.index('-model-cfg') + 1] = str(working / 'input.cfg')
                with mock.patch.object(sys, 'argv', ['stlmc'] + arguments):
                    cli = CliCommand(); cli.parse()
                common = cli.config.get_section('common')
                self.assertEqual(common.get_value('goal'), 'all')
                self.assertEqual(common.get_value('two-step'), 'false')
                self.assertEqual(common.get_value('reach'), 'false')
            finally:
                spawn.call_args.kwargs['stdout'].close()

    def worker(self, model, config):
        if importlib.util.find_spec('z3') is None:
            self.skipTest('Z3 is required for the UI execution regression')
        with tempfile.TemporaryDirectory() as directory:
            working = Path(directory)
            (working / 'input.model').write_text(model)
            request = self.api.RunRequest(model=model, config=config,
                solver='z3', bound=0, time_bound=1, threshold=0,
                goal='', two_step=False, reach=False)
            (working / 'input.cfg').write_text(self.api.effective_config(request))
            completed = subprocess.run([sys.executable, '-m', 'stlmc.ui.worker',
                'input.model', '-model-cfg', 'input.cfg', '-visualize'], cwd=working,
                env=dict(os.environ, PYTHONPATH=str(ROOT / 'src'), STLMC_DISABLE_UPDATE_CHECK='1'),
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
            self.assertEqual(completed.returncode, 0, completed.stdout)
            results = [json.loads(line) for line in (working / 'results.jsonl').read_text().splitlines()]
            return results, completed.stdout

    def test_real_worker_checks_all_goals_as_one_step_stl_when_form_clears_flags(self):
        model = '''[-1,2] x; {mode:true;inv:true;flow:d/dt[x]=0;jump:}
init:x=0;proposition:
goal:[f1]:[][0,1](x<=1); [f2]:[][0,1](x>=1);
'''
        results, output = self.worker(model,
            'common {goal="f1" two-step="true" reach="true"}')
        self.assertEqual([row['status'] for row in results], ['satisfied', 'violated'])
        self.assertEqual([row['bound'] for row in results], [0, 0])
        self.assertIn('one-step', output)
        self.assertNotIn('reachable', output)

    def test_model_reach_goal_remains_reachability_when_form_reach_is_false(self):
        model = '''[-1,2] x; {mode:true;inv:true;flow:d/dt[x]=0;jump:}
init:x=0;proposition:goal:reach(x>=0);
'''
        results, _ = self.worker(model, 'common {reach="true" two-step="true"}')
        self.assertEqual(results[0]['status'], 'reachable')
        self.assertEqual(results[0]['bound'], 0)

    def test_runtime_recovery_uses_released_package_not_mandatory_source_checkout(self):
        from stlmc.ui import runtime
        with mock.patch.object(runtime.importlib, 'import_module', side_effect=ImportError('missing')):
            result = runtime.inspect_runtime()
        self.assertIn('--upgrade --pre --force-reinstall --no-deps stlmc', result['error'])
        self.assertIn('restart stlmc-gui', result['error'])
        self.assertNotIn('-e /path/to/stlmc', result['error'])

    def test_pairing_output_contains_each_url_once_and_never_redirected_token(self):
        from stlmc.ui.bridge import show_pairing
        terminal = io.StringIO()
        terminal.isatty = lambda: True
        redirected = io.StringIO()
        with mock.patch('sys.stderr', terminal), mock.patch('sys.stdout', redirected):
            show_pairing('test-session-token', ['http://127.0.0.1:8766',
                         'http://localhost:8766', 'https://example.org'], 8765,
                         workspace_url='http://127.0.0.1:8766/')
        self.assertEqual(terminal.getvalue().count('http://127.0.0.1:8765'), 1)
        self.assertEqual(terminal.getvalue().count('http://127.0.0.1:8766'), 1)
        self.assertIn('https://example.org', terminal.getvalue())
        self.assertEqual(redirected.getvalue(), '')


if __name__ == '__main__':
    unittest.main()
