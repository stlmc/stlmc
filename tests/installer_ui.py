"""UI dependency selection stays optional and uninstall retains user data."""
import io
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

from stlmc.cli import installer, uninstall
from stlmc.cli.dependency_policy import UI_PACKAGES, UI_UNINSTALL_PACKAGES


class UiInstallerTest(unittest.TestCase):
    def test_ui_only_install_and_check_do_not_select_solvers_or_visualization(self):
        for action in ('install', 'check'):
            with self.subTest(action=action), mock.patch.object(installer, '_ui', return_value=0) as ui, \
                    mock.patch.object(installer.solvers, 'main') as solver, \
                    mock.patch.object(installer, '_visualize') as visual:
                self.assertEqual(installer.main([action, '--ui']), 0)
                ui.assert_called_once_with(check=action == 'check')
                solver.assert_not_called()
                visual.assert_not_called()

    def test_ui_can_be_combined_with_selected_solver_and_visualization(self):
        with mock.patch.object(installer, '_ui', return_value=0) as ui, \
                mock.patch.object(installer.solvers, 'main', return_value=0) as solver, \
                mock.patch.object(installer, '_visualize', return_value=0) as visual:
            self.assertEqual(installer.main(['install', '--ui', '--solver', 'z3', '--visualize', 'html']), 0)
        ui.assert_called_once_with(check=False)
        solver.assert_called_once_with(['z3'])
        visual.assert_called_once_with(check=False, output_format='html', status_cache=mock.ANY)

    def test_ui_is_not_implicitly_installed_with_solver(self):
        with mock.patch.object(installer, '_ui') as ui, \
                mock.patch.object(installer.solvers, 'main', return_value=0):
            self.assertEqual(installer.main(['install', '--solver', 'z3']), 0)
            ui.assert_not_called()

    def test_ui_invalid_selections_fail_before_side_effects(self):
        for args in (['install', '--ui', '--ui'], ['check', '--all', '--ui'],
                     ['install', '--solver', 'yices', '--ui', '--build'],
                     ['install', '--solver', 'dreal', '--ui', '--experimental-build']):
            with self.subTest(args=args), mock.patch('sys.stderr', io.StringIO()), \
                    mock.patch.object(installer, '_ui') as ui, \
                    mock.patch.object(installer.solvers, 'main') as solver:
                with self.assertRaises(SystemExit):
                    installer.main(args)
                ui.assert_not_called()
                solver.assert_not_called()

    def test_ui_check_does_not_install_and_reports_missing(self):
        with mock.patch.object(installer.solvers, '_python_package_status', return_value=(False, 'missing')), \
                mock.patch.object(installer.solvers, '_install_python_package') as pip:
            self.assertEqual(installer._ui(check=True), 1)
        pip.assert_not_called()

    def test_ui_repairs_pinned_dependencies_then_checks_fresh_interpreter(self):
        statuses = [(False, 'missing'), (True, 'pinned')] * len(UI_PACKAGES)
        with mock.patch.object(installer.solvers, '_python_package_status', side_effect=statuses), \
                mock.patch.object(installer.solvers, '_install_python_package') as pip, \
                mock.patch.object(installer.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, 'ok\n', '')) as smoke:
            self.assertEqual(installer._ui(), 0)
        self.assertEqual(pip.call_args_list, [mock.call(spec) for spec in UI_PACKAGES.values()])
        self.assertEqual(smoke.call_args.args[0][0], installer.sys.executable)

    def test_ui_smoke_failure_is_reported(self):
        with mock.patch.object(installer.solvers, '_python_package_status', return_value=(True, 'pinned')), \
                mock.patch.object(installer.subprocess, 'run', return_value=subprocess.CompletedProcess([], 1, '', 'incompatible')), \
                mock.patch('sys.stderr', io.StringIO()) as error:
            self.assertEqual(installer._ui(check=True), 1)
        self.assertIn('incompatible', error.getvalue())

    def test_ui_uninstall_routes_only_ui_and_preserves_shared_dependencies(self):
        with mock.patch.object(uninstall, 'plan_uninstall', return_value=uninstall.UninstallPlan()) as plan, \
                mock.patch.object(uninstall, 'execute_uninstall', return_value=0) as execute:
            self.assertEqual(installer.main(['uninstall', '--ui', '--dry-run']), 0)
        plan.assert_called_once_with([], [], ui=True)
        self.assertTrue(execute.call_args.args[1])
        with tempfile.TemporaryDirectory() as temporary:
            prefix = Path(temporary) / 'venv'
            distribution = SimpleNamespace(locate_file=lambda _: prefix / 'lib/site-packages')
            with mock.patch.object(uninstall.sys, 'prefix', str(prefix)), \
                    mock.patch.object(uninstall.sys, 'base_prefix', '/base'), \
                    mock.patch.object(uninstall, 'distribution', return_value=distribution), \
                    mock.patch.object(uninstall, 'solver_data_dir', return_value=Path(temporary) / 'managed'):
                result = uninstall.plan_uninstall([], [], ui=True)
        self.assertEqual(result.packages, list(UI_UNINSTALL_PACKAGES))
        self.assertTrue({'packaging', 'numpy', 'scipy', 'stlmc', 'anyio', 'pydantic-core'}.isdisjoint(result.packages))
        self.assertTrue(any('models' in note and 'run results' in note for note in result.notes))

    def test_ui_pins_packaged_assets_and_base_dependencies(self):
        import tomllib
        root = Path(__file__).resolve().parent.parent
        config = tomllib.loads((root / 'pyproject.toml').read_text())
        base = config['project']['dependencies']
        self.assertFalse(any(spec.startswith(tuple(name + '==' for name in UI_PACKAGES)) for spec in base))
        constraints = Path(installer.__file__).with_name('dependency-constraints.txt').read_text().splitlines()
        self.assertTrue(set(UI_PACKAGES.values()) <= set(constraints))
        self.assertIn('pydantic-core==2.50.1', constraints)
        self.assertIn('ui/static/**/*', config['tool']['setuptools']['package-data']['stlmc'])


if __name__ == '__main__':
    unittest.main()
