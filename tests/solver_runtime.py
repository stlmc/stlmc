"""Optional solver discovery, native feature guards, and solver-free CLI use."""

import ctypes.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT/'src'))

from stlmc.exceptions import SolverUnavailableError
from stlmc.solver.availability import load_yices_binding, selected_yices_library


class YicesExecutionGuardTest(unittest.TestCase):
    def setUp(self):
        try:
            from stlmc.solver.yices import YicesSolver
        except (ImportError, OSError, SolverUnavailableError) as error:
            self.skipTest(str(error))
        from stlmc.parser.config_visitor import ConfigVisitor
        self.adapter = YicesSolver
        # Patch the class itself: newer unittest.mock resolves the dotted
        # 'yices.Yices' path to the same-named module, not this exported class.
        self.yices_api = load_yices_binding().Yices
        self.config = ConfigVisitor().parse_from_file(str(ROOT/'src/stlmc/default.cfg'))
        self.config.get_section('yices').set_value('logic', 'QF_LRA')

    def test_unsafe_parallel_is_rejected_even_with_one_worker(self):
        common = self.config.get_section('common')
        common.set_value('parallel', 'true')
        for workers in ('1', '8'):
            common.set_value('parallel-core', workers)
            with self.subTest(workers=workers), mock.patch.object(self.yices_api, 'is_thread_safe', return_value=False):
                with self.assertRaisesRegex(SolverUnavailableError, 'thread-safe.*stlmc-installer install --solver yices'):
                    self.adapter(self.config)
        self.assertEqual(common.get_value('parallel'), 'true')

    def test_unsafe_library_allows_explicit_sequential_execution(self):
        self.config.get_section('common').set_value('parallel', 'false')
        with mock.patch.object(self.yices_api, 'is_thread_safe', return_value=False):
            self.adapter(self.config)

    def test_thread_safe_library_allows_parallel_configuration(self):
        self.config.get_section('common').set_value('parallel', 'true')
        # Configuration policy only: never run unsafe native calls under a
        # mocked capability. Native concurrency needs a real thread-safe build.
        with mock.patch.object(self.yices_api, 'is_thread_safe', return_value=True):
            self.adapter(self.config)

    def test_nonlinear_logic_requires_mcsat(self):
        self.config.get_section('yices').set_value('logic', 'QF_NRA')
        with mock.patch.object(self.yices_api, 'has_mcsat', return_value=False):
            with self.assertRaisesRegex(SolverUnavailableError, 'requires MCSAT.*without-mcsat'):
                self.adapter(self.config)

    def test_nonlinear_parallel_needs_both_capabilities(self):
        self.config.get_section('common').set_value('parallel', 'true')
        self.config.get_section('yices').set_value('logic', 'QF_NRA')
        with mock.patch.object(self.yices_api, 'is_thread_safe', return_value=True), \
                mock.patch.object(self.yices_api, 'has_mcsat', return_value=True):
            self.adapter(self.config)

    def test_configuration_change_cannot_bypass_pre_worker_guard(self):
        self.config.get_section('common').set_value('parallel', 'false')
        with mock.patch.object(self.yices_api, 'is_thread_safe', return_value=False):
            solver = self.adapter(self.config)
            self.config.get_section('common').set_value('parallel', 'true')
            with mock.patch('stlmc.solver.yices.ThreadWorker') as worker:
                with self.assertRaisesRegex(SolverUnavailableError, 'thread-safe'):
                    solver.submit(None)
                worker.assert_not_called()


class YicesDiscoveryTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        # macOS intentionally ignores XDG_DATA_HOME. Never inspect a real
        # managed installation while testing discovery with fake libraries.
        patch = mock.patch('stlmc.solver.availability.solver_data_dir',
                           return_value=Path(temporary.name).resolve())
        patch.start()
        self.addCleanup(patch.stop)

    def test_override_precedes_manifest_and_invalid_selection_does_not_fall_back(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            library = root/'libyices.so'
            library.touch()
            with mock.patch.dict(os.environ, {'STLMC_YICES_LIBRARY': str(library), 'XDG_DATA_HOME': tmp}):
                self.assertEqual(selected_yices_library(), str(library))
            with mock.patch.dict(os.environ, {'STLMC_YICES_LIBRARY': str(root/'missing')}):
                with self.assertRaisesRegex(SolverUnavailableError, 'not found'):
                    selected_yices_library()

    def test_active_manifest_and_system_fallback(self):
        with tempfile.TemporaryDirectory() as tmp:
            library = Path(tmp).resolve()/'native.so'
            library.touch()
            data_dir = Path(tmp).resolve()/'stlmc/solvers'
            manifest = data_dir/'yices/active.json'
            manifest.parent.mkdir(parents=True)
            with mock.patch.dict(os.environ, {'XDG_DATA_HOME': tmp}), \
                    mock.patch('stlmc.solver.availability.solver_data_dir',
                               return_value=data_dir):
                os.environ.pop('STLMC_YICES_LIBRARY', None)
                self.assertIsNone(selected_yices_library())
                manifest.write_text(json.dumps({'library': str(library)}))
                self.assertEqual(selected_yices_library(), str(library))
                manifest.write_text('{}')
                with self.assertRaisesRegex(SolverUnavailableError, 'invalid Yices installation manifest'):
                    selected_yices_library()

    def test_bootstrap_override_is_limited_to_import(self):
        with tempfile.TemporaryDirectory() as tmp:
            library = Path(tmp).resolve()/'native.so'
            library.touch()
            binding = SimpleNamespace()
            def import_binding(name):
                self.assertEqual(name, 'yices')
                self.assertEqual(ctypes.util.find_library('yices'), str(library))
                self.assertEqual(ctypes.util.find_library('other'), 'system-other')
                return binding
            with mock.patch.dict(os.environ, {'STLMC_YICES_LIBRARY': str(library)}), \
                    mock.patch.dict(sys.modules), \
                    mock.patch('stlmc.solver.availability._yices_managed_selection', None), \
                    mock.patch('stlmc.solver.availability._yices_dependency_handles', {}), \
                    mock.patch('ctypes.util.find_library', return_value='system-other') as original, \
                    mock.patch('importlib.import_module', side_effect=import_binding):
                sys.modules.pop('yices', None)
                sys.modules.pop('yices_api', None)
                sys.modules.pop('cvc5', None)
                self.assertIs(load_yices_binding(), binding)
                self.assertIs(ctypes.util.find_library, original)

    def test_cannot_replace_a_live_library(self):
        with tempfile.TemporaryDirectory() as tmp:
            library = Path(tmp).resolve()/'new.so'
            library.touch()
            with mock.patch.dict(os.environ, {'STLMC_YICES_LIBRARY': str(library)}), \
                    mock.patch.dict(sys.modules, {'yices': SimpleNamespace(),
                        'yices_api': SimpleNamespace(libyices=SimpleNamespace(_name='/old/native.so'))}):
                with self.assertRaisesRegex(SolverUnavailableError, 'restart the process'):
                    load_yices_binding()

    def test_late_native_initialization_is_rejected_after_cvc5(self):
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.dict(os.environ, {'XDG_DATA_HOME': tmp}), \
                mock.patch.dict(sys.modules, {'cvc5': SimpleNamespace()}):
            os.environ.pop('STLMC_YICES_LIBRARY', None)
            sys.modules.pop('yices', None)
            with self.assertRaisesRegex(SolverUnavailableError, 'initialized before.*restart'):
                load_yices_binding()


BLOCK_IMPORTS = '''
import importlib.abc, sys
class BlockSolvers(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname.split('.')[0] in BLOCKED:
            raise ModuleNotFoundError('test blocked ' + fullname, name=fullname)
sys.meta_path.insert(0, BlockSolvers())
'''


class SolverFreeCliTest(unittest.TestCase):
    def run_child(self, script, blocked=('z3', 'yices', 'yices_api', 'cvc5'), env=None):
        environment = dict(os.environ, PYTHONPATH=str(ROOT/'src'))
        environment.update(env or {})
        code = 'BLOCKED = ' + repr(blocked) + '\n' + BLOCK_IMPORTS + '\n' + script
        return subprocess.run([sys.executable, '-c', code], env=environment,
                              text=True, capture_output=True, timeout=20)

    def test_help_does_not_require_any_solver(self):
        for module in ('mc', 'visualize'):
            result = self.run_child("sys.argv=['stlmc','-h'];from stlmc.cli." + module + " import main;main()")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('usage:', result.stdout.lower())

    def test_missing_selected_backend_has_installer_hint(self):
        for backend in ('z3', 'yices', 'cvc5'):
            result = self.run_child('''
from stlmc.solver.solver_factory import SolverFactory
from stlmc.exceptions import SolverUnavailableError
try:
    SolverFactory().generate_formula_solver_factory(BACKEND)
except SolverUnavailableError as error:
    print(error)
else:
    raise AssertionError('missing backend was accepted')
'''.replace('BACKEND', repr(backend)))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('stlmc-installer install --solver ' + backend, result.stdout)

    def test_optional_quantifier_elimination_dependency_is_explicit(self):
        result = self.run_child('''
from stlmc.constraints.quantified_flow import eliminate_boolean_flow_condition
from stlmc.exceptions import SolverUnavailableError
try:
    eliminate_boolean_flow_condition(None)
except SolverUnavailableError as error:
    print(error)
''', blocked=('z3',))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('stlmc-installer install --solver z3', result.stdout)

    def test_missing_default_core_backend_has_role_and_installer_hint(self):
        result = self.run_child('''
from stlmc.solver.solver_factory import SolverFactory
from stlmc.exceptions import SolverUnavailableError
try:
    SolverFactory().generate_core_solver_factory()
except SolverUnavailableError as error:
    print(error)
''', env={'STLMC_CORE_SOLVER': 'z3'})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('core solving', result.stdout)
        self.assertIn('stlmc-installer install --solver z3', result.stdout)

    def test_yices_only_verification_does_not_import_z3(self):
        try:
            from stlmc.solver.availability import load_yices_binding
            load_yices_binding()
        except Exception as error:
            self.skipTest(str(error))
        with tempfile.TemporaryDirectory() as tmp:
            model = Path(tmp)/'case.model'
            config = Path(tmp)/'case.cfg'
            model.write_text('''[0, 2] x;
{ mode: true; inv: x <= 2; flow: d/dt[x] = 1; jump: }
init: x = 0;
proposition:
goal: [g]: [][0,1] (x <= 2);
''')
            config.write_text('''common { solver = "yices" bound = 0 time-bound = 1 two-step = "true" parallel = "false" }
yices { logic = "QF_LRA" }
''')
            result = self.run_child('''
from stlmc.cli.mc import main
sys.argv=['stlmc', MODEL, '-model-cfg', CONFIG]
status=main()
assert 'z3' not in sys.modules
sys.exit(status)
'''.replace('MODEL', repr(str(model))).replace('CONFIG', repr(str(config))),
                blocked=('z3',), env={'STLMC_SCENARIO_SOLVER': 'yices', 'STLMC_CORE_SOLVER': 'yices'})
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('satisfied', result.stdout)


if __name__ == '__main__':
    unittest.main()
