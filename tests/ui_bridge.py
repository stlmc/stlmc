"""Optional UI API security and package-local worker contracts."""
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))


class UiPackageTest(unittest.TestCase):
    def test_gui_help_is_lazy_and_has_a_distinct_program_name(self):
        script = '''
import importlib.abc, sys
class BlockUI(importlib.abc.MetaPathFinder):
 def find_spec(self, fullname, path=None, target=None):
  if fullname.split('.')[0] in {'fastapi','uvicorn','pydantic','nicegui'}:
   raise RuntimeError('optional UI imported: '+fullname)
sys.meta_path.insert(0,BlockUI())
from stlmc.cli.ui import main
sys.argv=['stlmc-gui','--help']
raise SystemExit(main())
'''
        completed = subprocess.run([sys.executable, '-c', script],
            env=dict(os.environ, PYTHONPATH=str(ROOT / 'src')), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=15)
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn('--ui-port', completed.stdout)
        self.assertIn('--allow-origin', completed.stdout)
        self.assertIn('--no-auth', completed.stdout)
        self.assertIn('--models-dir', completed.stdout)
        self.assertIn('--runs-dir', completed.stdout)
        self.assertIn('usage: stlmc-gui', completed.stdout)

    def test_no_auth_rejects_hosted_origin_before_loading_optional_dependencies(self):
        completed = subprocess.run([sys.executable, '-m', 'stlmc.cli.ui', '--no-auth',
                                    '--allow-origin', 'https://stlmc.github.io'],
            env=dict(os.environ, PYTHONPATH=str(ROOT / 'src')), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=15)
        self.assertEqual(completed.returncode, 2)
        self.assertIn('--no-auth cannot be combined with --allow-origin', completed.stdout)

    def test_ui_missing_dependencies_provide_installer_command(self):
        script = '''
import importlib.abc, sys
class BlockUI(importlib.abc.MetaPathFinder):
 def find_spec(self, fullname, path=None, target=None):
  if fullname.split('.')[0] in {'fastapi','uvicorn','pydantic','nicegui'}:
   raise ModuleNotFoundError(fullname)
sys.meta_path.insert(0,BlockUI())
from stlmc.cli.ui import main
sys.argv=['stlmc-gui','--no-browser']
raise SystemExit(main())
'''
        completed = subprocess.run([sys.executable, '-c', script],
            env=dict(os.environ, PYTHONPATH=str(ROOT / 'src')), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=15)
        self.assertEqual(completed.returncode, 2, completed.stdout)
        self.assertIn('stlmc-installer install --ui', completed.stdout)

    def test_worker_module_uses_the_current_interpreter_without_ui_dependencies(self):
        completed = subprocess.run([sys.executable, '-m', 'stlmc.ui.worker', '--check-runtime'],
            env=dict(os.environ, PYTHONPATH=str(ROOT / 'src')), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        result = json.loads(completed.stdout)
        self.assertEqual(result['executable'], sys.executable)
        self.assertIn('stlmc', result)

    def test_paths_use_user_data_not_package_directory(self):
        from stlmc.ui.paths import data_dir
        with mock.patch.dict(os.environ, {'XDG_DATA_HOME': '/user-owned-data'}), \
                mock.patch('stlmc.ui.paths.sys.platform', 'linux'):
            self.assertEqual(data_dir(), Path('/user-owned-data/stlmc/ui'))

    def test_examples_seed_without_overwriting_user_edits(self):
        from stlmc.ui.paths import seed_examples
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            seed_examples(root)
            model = root / 'therm-tutorial.model'
            self.assertTrue(model.is_file())
            model.write_text('user edits')
            seed_examples(root)
            self.assertEqual(model.read_text(), 'user edits')

    def test_plain_cli_help_does_not_import_optional_ui(self):
        script = '''
import importlib.abc, sys
class BlockUI(importlib.abc.MetaPathFinder):
 def find_spec(self, fullname, path=None, target=None):
  if fullname.split('.')[0] in {'fastapi','uvicorn','pydantic','nicegui'}:
   raise RuntimeError('optional UI imported: '+fullname)
sys.meta_path.insert(0,BlockUI())
from stlmc.cli.mc import main
sys.argv=['stlmc','-h']
raise SystemExit(main())
'''
        completed = subprocess.run([sys.executable, '-c', script],
            env=dict(os.environ, PYTHONPATH=str(ROOT / 'src')), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=15)
        self.assertEqual(completed.returncode, 0, completed.stdout)


class UiBridgeSecurityTest(unittest.TestCase):
    TOKEN = 'test-only-session-token-' * 3
    ORIGIN = 'https://stlmc.github.io'

    def setUp(self):
        try:
            from fastapi.testclient import TestClient
            self.bridge = importlib.import_module('stlmc.ui.bridge')
        except ImportError as error:
            self.skipTest('Optional UI test dependencies are unavailable: ' + str(error))
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        # Production canonicalizes RUNS. macOS temporary paths may begin with
        # /var, which is a symlink to /private/var; keep that system alias out
        # of the no-follow path fixture while testing actual malicious links.
        for name, value in [('RUNS', Path(temporary.name).resolve() / 'runs'), ('JOBS', {}),
                            ('health', lambda: {'stlmc': True})]:
            patch = mock.patch.object(self.bridge.local, name, value)
            patch.start(); self.addCleanup(patch.stop)
        self.client = TestClient(self.bridge.create_app(token=self.TOKEN, allow_origins=[self.ORIGIN]),
            base_url='http://127.0.0.1:8765',
            headers={'Origin': self.ORIGIN, 'Authorization': 'Bearer ' + self.TOKEN})
        self.runs = self.bridge.local.RUNS
        self.addCleanup(self.client.close)

    def test_protocol_and_authentication(self):
        self.assertEqual(self.client.get('/api/bridge').json()['protocol'], 1)
        for path in ['/api/bridge', '/api/health', '/api/runs', '/api/documents']:
            with self.subTest(path=path):
                self.assertEqual(self.client.get(path, headers={'Authorization': 'Bearer wrong'}).status_code, 401)

    def test_no_auth_is_explicit_and_still_guards_host_origin_and_query(self):
        from fastapi.testclient import TestClient
        origin = 'http://127.0.0.1:18080'
        with TestClient(self.bridge.create_app(auth_required=False, allow_origins=[origin]),
                        base_url='http://127.0.0.1:8765', headers={'Origin': origin}) as client:
            response = client.get('/api/bridge')
            self.assertEqual(response.status_code, 200)
            self.assertFalse(response.json()['auth_required'])
            self.assertEqual(client.get('/api/bridge', headers={'Host': 'evil.example'}).status_code, 403)
            self.assertEqual(client.get('/api/bridge', headers={'Origin': 'https://evil.example'}).status_code, 403)
            self.assertEqual(client.get('/api/bridge?token=secret').status_code, 400)
        with self.assertRaises(ValueError):
            self.bridge.create_app(auth_required=False, allow_origins=[self.ORIGIN])

    def test_input_inspection_uses_stlmc_defaults_and_is_guarded(self):
        response = self.client.post('/api/inspect', json={'model': '', 'config': ''})
        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.json()['common']['solver'], 'auto')
        self.assertNotIn('bound', response.json()['common'])
        self.assertNotIn('smt2-dir', response.json()['common'])
        self.assertEqual(self.client.post('/api/inspect', json={},
            headers={'Authorization': 'Bearer wrong'}).status_code, 401)
        self.assertEqual(self.client.post('/api/inspect', json={
            'config': 'dreal {executable-path="/tmp/unsafe"}'}).status_code, 422)
        invalid = self.client.post('/api/inspect', json={'config': 'common {not-an-option=1}'})
        self.assertEqual(invalid.status_code, 200)
        self.assertIsNone(invalid.json()['common'])
        self.assertEqual(invalid.json()['diagnostics'][0]['source'], 'config')

    def test_inspection_syntax_error_has_location_without_validation_json(self):
        response = self.client.post('/api/inspect', json={'config': 'common {\nthreshold=0.1\n};'})
        self.assertEqual(response.status_code, 200)
        issue = response.json()['diagnostics'][0]
        self.assertEqual((issue['source'], issue['line'], issue['column']), ('config', 3, 2))
        self.assertIn("unexpected ';'", issue['message'])
        self.assertNotIn('input', issue)

    def test_document_watch_tracks_add_change_remove_without_reading_bodies(self):
        folder = self.runs.parent / 'models'; folder.mkdir()
        with mock.patch.object(self.bridge.local.documents, 'DIRECTORY', folder):
            target = folder / 'watch.model'; target.write_text('first')
            original = target.stat()
            before = self.client.get('/api/documents/watch').json()
            self.assertEqual(before['model'][0]['name'], 'watch.model')
            self.assertNotIn('text', before['model'][0])
            target.write_text('other')
            os.utime(target, ns=(original.st_atime_ns, original.st_mtime_ns))
            after = self.client.get('/api/documents/watch').json()
            self.assertNotEqual(before['model'][0]['version'], after['model'][0]['version'])
            (folder / 'settings.cfg').write_text('common {}')
            target.unlink()
            final = self.client.get('/api/documents/watch').json()
            self.assertEqual(final['model'], [])
            self.assertEqual(final['cfg'][0]['name'], 'settings.cfg')

    def test_clear_history_keeps_active_run_and_models(self):
        ids = ['a' * 32, 'b' * 32]
        for name in ids:
            folder = self.runs / name
            folder.mkdir(parents=True)
            (folder / 'job.json').write_text(json.dumps({'id': name, 'started': 1, 'state': 'completed'}))
            (folder / 'run.log').write_text('log')
        with mock.patch.object(self.bridge.local, 'ACTIVE', ids[1]):
            response = self.client.post('/api/runs/clear', json={'run_ids': ids})
        self.assertEqual(response.status_code, 200, response.text)
        self.assertEqual(response.json(), {'deleted': [ids[0]], 'kept': [ids[1]]})
        self.assertFalse((self.runs / ids[0]).exists())
        self.assertTrue((self.runs / ids[1] / 'run.log').exists())

    def test_clear_history_rejects_traversal_and_symlinks_without_deleting_anything(self):
        name = 'c' * 32
        folder = self.runs / name; folder.mkdir(parents=True)
        (folder / 'job.json').write_text(json.dumps({'id': name, 'started': 1, 'state': 'completed'}))
        external = self.runs.parent / 'keep.model'; external.write_text('keep')
        (folder / 'link').symlink_to(external)
        self.assertEqual(self.client.post('/api/runs/clear', json={'run_ids': [name]}).status_code, 409)
        self.assertTrue((folder / 'job.json').exists())
        self.assertEqual(external.read_text(), 'keep')
        self.assertEqual(self.client.post('/api/runs/clear', json={'run_ids': ['../models']}).status_code, 422)
        self.assertEqual(self.client.post('/api/runs/clear', json={'run_ids': [name]},
            headers={'Authorization': 'Bearer wrong'}).status_code, 401)

    def test_clear_history_keeps_runs_owned_by_another_live_gui(self):
        name = 'd' * 32
        folder = self.runs / name; folder.mkdir(parents=True)
        (folder / 'job.json').write_text(json.dumps({'id': name, 'started': 1,
            'state': 'running', 'owner_pid': os.getpid()}))
        response = self.client.post('/api/runs/clear', json={'run_ids': [name]})
        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.json(), {'deleted': [], 'kept': [name]})
        self.assertTrue((folder / 'job.json').exists())

    def test_only_guarded_application_factory_is_exposed(self):
        self.assertFalse(hasattr(self.bridge.local, 'app'))
        self.assertFalse(hasattr(self.bridge.local.documents, 'router'))
        self.assertFalse(hasattr(self.bridge, 'main'))
        self.assertEqual(self.client.delete('/api/runs').status_code, 405)
        self.assertEqual(self.client.get('/api/bridge',
            headers={'Authorization': 'Bearer invalid'}).status_code, 401)

    def test_origin_host_and_url_tokens_rejected(self):
        for origin in ['null', 'https://evil.invalid', self.ORIGIN + '.evil.invalid']:
            self.assertEqual(self.client.get('/api/bridge', headers={'Origin': origin}).status_code, 403)
        self.assertEqual(self.client.get('/api/bridge', headers={'Host': 'evil.invalid'}).status_code, 403)
        self.assertEqual(self.client.get('/api/bridge?token=' + self.TOKEN).status_code, 400)
        self.client.headers.pop('Origin')
        self.assertEqual(self.client.get('/api/bridge').status_code, 403)

    def test_preflight_and_request_size_limits(self):
        response = self.client.options('/api/runs', headers={
            'Access-Control-Request-Method': 'POST',
            'Access-Control-Request-Headers': 'authorization,content-type',
            'Access-Control-Request-Private-Network': 'true'})
        self.assertEqual(response.status_code, 204)
        self.assertEqual(response.headers['access-control-allow-private-network'], 'true')
        self.assertEqual(self.client.post('/api/runs', content=b'x' * (self.bridge.MAX_BODY + 1)).status_code, 413)

    def test_executable_and_output_overrides_are_disabled(self):
        for key in ('executable-path', 'SAVE-SMT2', 'smt2-dir'):
            with self.subTest(key=key):
                response = self.client.post('/api/runs', json={'model': 'not executed',
                    'config': 'common { ' + key + '="/tmp/out" }'})
                self.assertEqual(response.status_code, 422)
        self.assertEqual(self.client.delete('/api/runs').status_code, 405)

    def test_nonfinite_values_return_json_validation_errors_without_starting_solver(self):
        for field in ('time_bound', 'threshold'):
            for value in ('NaN', 'Infinity', '-Infinity'):
                with self.subTest(field=field, value=value), \
                        mock.patch.object(self.bridge.local, 'start') as start:
                    response = self.client.post('/api/runs',
                        content='{"model":"not executed","' + field + '":' + value + '}',
                        headers={'Content-Type': 'application/json'})
                    self.assertEqual(response.status_code, 422)
                    self.assertTrue(response.json()['detail'])
                    start.assert_not_called()

    def test_run_and_artifact_symlinks_rejected(self):
        root = self.bridge.local.RUNS
        root.mkdir()
        outside = root.parent / 'outside'; outside.mkdir()
        (root / ('a' * 32)).symlink_to(outside, target_is_directory=True)
        self.assertEqual(self.client.get('/api/runs/' + 'a' * 32).status_code, 404)
        folder = root / ('b' * 32); folder.mkdir()
        (folder / 'job.json').write_text(json.dumps({'id': folder.name, 'started': 1, 'state': 'completed'}))
        (folder / 'secret.html').symlink_to(Path(__file__))
        response = self.client.get('/api/runs/' + folder.name)
        self.assertEqual(response.status_code, 200, response.text)
        self.assertNotIn('secret.html', response.json()['files'])
        self.assertEqual(self.client.get('/api/runs/' + folder.name + '/files/secret.html').status_code, 404)

    def test_ancestor_symlink_is_rejected_even_when_leaf_directory_is_regular(self):
        from fastapi.testclient import TestClient
        root = self.bridge.local.RUNS.parent
        actual = root / 'real-parent'; actual.mkdir()
        alias = root / 'linked-parent'; alias.symlink_to(actual, target_is_directory=True)
        run_id = 'c' * 32
        folder = actual / 'runs' / run_id; folder.mkdir(parents=True)
        (folder / 'job.json').write_text(json.dumps({'id': run_id, 'started': 1, 'state': 'completed'}))
        (folder / 'secret.html').write_text('private ancestor content')
        with mock.patch.object(self.bridge.local, 'RUNS', alias / 'runs'):
            client = TestClient(self.bridge.create_app(token=self.TOKEN, allow_origins=[self.ORIGIN]),
                base_url='http://127.0.0.1:8765',
                headers={'Origin': self.ORIGIN, 'Authorization': 'Bearer ' + self.TOKEN})
            try:
                for path in ['/api/runs', '/api/runs/' + run_id,
                             '/api/runs/' + run_id + '/files/secret.html']:
                    with self.subTest(path=path):
                        response = client.get(path)
                        self.assertEqual(response.status_code, 404)
                        self.assertNotIn('private ancestor content', response.text)
            finally:
                client.close()


if __name__ == '__main__':
    unittest.main()
