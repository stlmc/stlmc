"""Explicit uninstall selection and optional-package boundaries."""
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

from stlmc.cli import installer, uninstall
from stlmc.cli.install_receipts import file_hash, write_dreal_receipt, write_receipt


class UninstallRoutingTest(unittest.TestCase):
    def test_receipt_inventory_records_only_the_private_installed_files(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'private-release'
            root.mkdir()
            library = root / 'libyices.so'
            library.write_bytes(b'verified native library')
            receipt = write_receipt(root, 'yices-official')
            record = json.loads(receipt.read_text())
            self.assertEqual(record['files'], {'libyices.so': file_hash(library)})
            self.assertEqual(record['root'], str(root))
            self.assertEqual(record['managed_by'], 'stlmc-installer')

    def test_dreal_receipt_uses_verified_staged_bytes_without_changing_active_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target, staged = root / 'dReal', root / 'verified-staged'
            target.write_bytes(b'previous user file')
            staged.write_bytes(b'new verified solver')
            receipt = write_dreal_receipt(staged, target)
            record = json.loads(receipt.read_text())
            self.assertEqual(record['files'], {'dReal': file_hash(staged)})
            self.assertEqual(target.read_bytes(), b'previous user file')
            self.assertEqual(receipt.name, 'dreal-' + file_hash(staged) + '.json')

    def test_uninstall_routes_explicit_targets_and_dry_run(self):
        plan = uninstall.UninstallPlan()
        with mock.patch.object(uninstall, 'plan_uninstall', return_value=plan) as planning, \
                mock.patch.object(uninstall, 'execute_uninstall', return_value=0) as execution:
            self.assertEqual(installer.main(['uninstall', '--solver', 'yices', 'z3',
                                             '--visualize', 'html', 'pdf', '--dry-run']), 0)
        planning.assert_called_once_with(['yices', 'z3'], ['html', 'pdf'])
        execution.assert_called_once_with(plan, True)

    def test_all_expands_only_components_and_is_not_the_default(self):
        with mock.patch.object(uninstall, 'plan_uninstall', return_value=uninstall.UninstallPlan()) as planning, \
                mock.patch.object(uninstall, 'execute_uninstall', return_value=0):
            self.assertEqual(installer.main(['uninstall', '--all']), 0)
        planning.assert_called_once_with(['z3', 'cvc5', 'yices', 'dreal'], ['html', 'pdf', 'text'])
        with mock.patch('sys.stderr', io.StringIO()), self.assertRaises(SystemExit):
            installer.main(['uninstall'])

    def test_invalid_duplicate_mixed_and_build_flags_are_rejected_before_planning(self):
        invalid = [[], ['--all', '--all'], ['--all', '--solver', 'z3'],
                   ['--solver', 'yices', 'yices'], ['--visualize', 'html', '--visualize', 'pdf'],
                   ['--solver', 'yices', '--build'], ['--solver', 'yices', '--thread-safe']]
        for arguments in invalid:
            with self.subTest(arguments=arguments), mock.patch('sys.stderr', io.StringIO()), \
                    mock.patch.object(uninstall, 'plan_uninstall') as planning:
                with self.assertRaises(SystemExit):
                    installer.main(['uninstall', *arguments])
                planning.assert_not_called()

    def test_optional_top_level_packages_only_and_base_dependencies_preserved(self):
        with tempfile.TemporaryDirectory() as temporary:
            prefix = Path(temporary) / 'venv'
            installed = SimpleNamespace(locate_file=lambda _: prefix / 'lib/site-packages')
            with mock.patch.object(uninstall.sys, 'prefix', str(prefix)), \
                    mock.patch.object(uninstall.sys, 'base_prefix', '/base'), \
                    mock.patch.object(uninstall, 'distribution', return_value=installed), \
                    mock.patch.object(uninstall, 'solver_data_dir', return_value=Path(temporary) / 'managed'):
                plan = uninstall.plan_uninstall(['z3', 'cvc5', 'yices', 'dreal'], ['html', 'pdf', 'text'])
        self.assertEqual(plan.packages, ['z3-solver', 'cvc5', 'yices', 'bokeh', 'matplotlib'])
        self.assertTrue({'numpy', 'scipy', 'sympy', 'lark', 'stlmc'}.isdisjoint(plan.packages))

    def test_external_or_nonvenv_python_packages_are_not_uninstalled(self):
        installed = SimpleNamespace(locate_file=lambda _: '/external/site-packages')
        with mock.patch.object(uninstall, 'distribution', return_value=installed), \
                mock.patch.object(uninstall.sys, 'prefix', '/venv'), \
                mock.patch.object(uninstall.sys, 'base_prefix', '/base'):
            plan = uninstall.plan_uninstall(['z3'], ['html'])
        self.assertEqual(plan.packages, [])
        self.assertTrue(any('outside the active virtual environment' in note for note in plan.notes))

    def test_dry_run_never_spawns_pip_or_changes_native_files(self):
        plan = uninstall.UninstallPlan(packages=['bokeh'])
        with mock.patch.object(uninstall.subprocess, 'run') as command, \
                mock.patch.object(uninstall, '_remove_verified') as remove, \
                mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(uninstall.execute_uninstall(plan, dry_run=True), 0)
        command.assert_not_called()
        remove.assert_not_called()
        self.assertIn('Would uninstall pip package: bokeh', output.getvalue())

    def test_pip_uninstall_is_one_explicit_current_interpreter_command(self):
        plan = uninstall.UninstallPlan(packages=['z3-solver', 'bokeh'])
        with mock.patch.object(uninstall.subprocess, 'run') as command, \
                mock.patch('sys.stdout', io.StringIO()):
            self.assertEqual(uninstall.execute_uninstall(plan), 0)
        command.assert_called_once_with(
            [uninstall.sys.executable, '-m', 'pip', 'uninstall', '--yes', 'z3-solver', 'bokeh'], check=True)


if __name__ == '__main__':
    unittest.main()
