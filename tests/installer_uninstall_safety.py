"""Destructive safety checks use only isolated temporary installations."""

from contextlib import ExitStack
import io
import hashlib
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
sys.path.insert(0, str(ROOT / 'src'))

from stlmc.cli import install_receipts, installer, uninstall


@unittest.skipUnless(os.name == 'posix', 'Native uninstall supports Linux and macOS')
class UninstallSafetyTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='stlmc-uninstall-safety-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.data = self.root / 'data with spaces'
        self.solvers = self.data / 'stlmc/solvers'
        self.release = self.solvers / ('yices/releases/yices-2.7.0-' + 'a' * 32)
        self.library = self.release / 'yices-2.7.0/lib/libyices.so.2.7.0'
        self.library.parent.mkdir(parents=True)
        self.library.write_bytes(b'owned native library')
        self.license = self.release / 'LICENSE'
        self.license.write_text('fixture license')
        install_receipts.write_receipt(self.release, 'yices-official')
        self.active = self.solvers / 'yices/active.json'
        self.active.write_text(json.dumps({
            'library': str(self.library), 'prefix': str(self.release / 'yices-2.7.0'),
            'version': '2.7.0', 'installation': 'official-binary',
        }))
        self.environment = mock.patch.dict(os.environ, {'XDG_DATA_HOME': str(self.data)})
        self.environment.start()
        self.addCleanup(self.environment.stop)
        os.environ.pop('STLMC_YICES_LIBRARY', None)
        self.platform = mock.patch('sys.platform', 'linux')
        self.platform.start()
        self.addCleanup(self.platform.stop)
        self.process = mock.patch('subprocess.run', return_value=subprocess.CompletedProcess([], 0, '', ''))
        self.process_mock = self.process.start()
        self.addCleanup(self.process.stop)

    def execute(self, solvers=('yices',), visuals=(), dry_run=False):
        with mock.patch('sys.stdout', new=io.StringIO()), mock.patch('sys.stderr', new=io.StringIO()):
            plan = uninstall.plan_uninstall(list(solvers), list(visuals))
            return uninstall.execute_uninstall(plan, dry_run=dry_run)

    def test_dry_run_invokes_no_mutating_operations_or_subprocesses(self):
        with ExitStack() as stack:
            mutations = [self.process_mock]
            for target in ('os.unlink', 'os.remove', 'os.rmdir', 'os.rename', 'os.replace',
                           'shutil.rmtree', 'shutil.move', 'pathlib.Path.unlink',
                           'pathlib.Path.rmdir', 'pathlib.Path.write_text'):
                mutations.append(stack.enter_context(mock.patch(target)))
            self.execute(solvers=('yices', 'dreal', 'z3', 'cvc5'), visuals=('html', 'pdf'), dry_run=True)
            for operation in mutations:
                operation.assert_not_called()
        self.assertTrue(self.library.exists())
        self.assertTrue(self.active.exists())

    def test_owned_native_files_are_removed_but_untracked_results_are_preserved(self):
        result = self.release / 'my.counterexample'
        result.write_bytes(b'user verification result')
        model = self.release / 'my.model'
        model.write_text('user model')
        self.execute()
        self.assertFalse(self.library.exists())
        self.assertEqual(result.read_bytes(), b'user verification result')
        self.assertEqual(model.read_text(), 'user model')

    def test_modified_recorded_files_are_preserved(self):
        self.library.write_bytes(b'changed after installation')
        self.execute()
        self.assertEqual(self.library.read_bytes(), b'changed after installation')

    def test_dry_run_plan_does_not_claim_modified_files_will_be_removed(self):
        self.library.write_bytes(b'changed after installation')
        plan = uninstall.plan_uninstall(['yices'], [])
        self.assertNotIn(self.library, [item.path for item in plan.removals])
        self.assertTrue(any('changed' in note.lower() or 'modified' in note.lower()
                            for note in plan.notes))

    def test_explicit_external_library_is_never_deleted(self):
        external = self.root / 'external-libyices.so'
        external.write_bytes(b'external user library')
        os.environ['STLMC_YICES_LIBRARY'] = str(external)
        self.execute()
        self.assertEqual(external.read_bytes(), b'external user library')

    def test_active_manifest_cannot_authorize_external_prefix_deletion(self):
        external = self.root / 'external custom build'
        library = external / 'lib/libyices.so'
        library.parent.mkdir(parents=True)
        library.write_bytes(b'external custom native')
        self.active.write_text(json.dumps({'library': str(library), 'prefix': str(external)}))
        self.execute()
        self.assertEqual(library.read_bytes(), b'external custom native')

    def test_legacy_receiptless_installation_is_not_recursively_deleted(self):
        (self.release / '.stlmc-install.json').unlink()
        self.execute()
        self.assertTrue(self.library.exists())

    def test_static_symlink_escape_cannot_delete_an_external_library(self):
        foreign = self.root / 'foreign'
        foreign.mkdir()
        foreign_library = foreign / self.library.name
        foreign_library.write_bytes(self.library.read_bytes())
        held = self.release / 'old-lib'
        self.library.parent.rename(held)
        self.library.parent.symlink_to(foreign, target_is_directory=True)
        self.execute()
        self.assertEqual(foreign_library.read_bytes(), b'owned native library')

    def test_parent_symlink_swap_at_unlink_cannot_escape_managed_root(self):
        plan = uninstall.plan_uninstall(['yices'], [])
        foreign = self.root / 'foreign'
        foreign.mkdir()
        foreign_library = foreign / self.library.name
        foreign_library.write_bytes(self.library.read_bytes())
        original_unlink = os.unlink
        swapped = []
        parent = self.library.parent
        held = self.release / 'held-lib'
        def swap_before_unlink(path, *args, **kwargs):
            if Path(os.fsdecode(path)).name == self.library.name and not swapped:
                parent.rename(held)
                parent.symlink_to(foreign, target_is_directory=True)
                swapped.append(True)
            return original_unlink(path, *args, **kwargs)
        with mock.patch('os.unlink', side_effect=swap_before_unlink) as patched_unlink:
            with mock.patch.object(os, 'supports_dir_fd', os.supports_dir_fd | {patched_unlink}), \
                    mock.patch('sys.stdout', new=io.StringIO()), mock.patch('sys.stderr', new=io.StringIO()):
                uninstall.execute_uninstall(plan)
        self.assertTrue(swapped, 'The race injection must actually run')
        self.assertEqual(foreign_library.read_bytes(), b'owned native library')

    def test_visualization_uninstall_never_selects_base_numerical_dependencies(self):
        prefix = self.root / 'venv'
        installed = SimpleNamespace(locate_file=lambda _: prefix / 'lib/site-packages')
        with mock.patch.object(uninstall.sys, 'prefix', str(prefix)), \
                mock.patch.object(uninstall.sys, 'base_prefix', str(self.root / 'base')), \
                mock.patch.object(uninstall, 'distribution', return_value=installed):
            self.execute(solvers=(), visuals=('html', 'pdf'))
        removed = [str(value).lower() for call in self.process_mock.call_args_list
                   for value in call.args[0]]
        self.assertIn('bokeh', removed)
        self.assertIn('matplotlib', removed)
        for package in ('numpy', 'scipy', 'sympy', 'mpmath', 'lark'):
            self.assertNotIn(package, removed)

    def test_receipt_traversal_never_authorizes_external_deletion(self):
        external = self.root / 'important.model'
        external.write_text('preserve this user model')
        receipt = self.release / '.stlmc-install.json'
        inventory = json.loads(receipt.read_text())
        relative_escape = os.path.relpath(external, self.release)
        inventory['files'][relative_escape] = hashlib.sha256(external.read_bytes()).hexdigest()
        receipt.write_text(json.dumps(inventory))
        self.execute()
        self.assertEqual(external.read_text(), 'preserve this user model')

    def test_activation_unlink_failure_keeps_its_native_library_intact(self):
        original_unlink = os.unlink
        attempts = []
        def deny_active(path, *args, **kwargs):
            if Path(os.fsdecode(path)).name == 'active.json':
                attempts.append(True)
                raise PermissionError('activation is not writable')
            return original_unlink(path, *args, **kwargs)
        with mock.patch('os.unlink', side_effect=deny_active) as patched_unlink:
            with mock.patch.object(os, 'supports_dir_fd', os.supports_dir_fd | {patched_unlink}):
                status = self.execute()
        self.assertTrue(attempts)
        self.assertNotEqual(status, 0)
        self.assertTrue(self.active.exists())
        self.assertTrue(self.library.exists())

    def test_partial_native_failure_retains_receipt_and_can_be_retried(self):
        original_unlink = os.unlink
        def deny_library(path, *args, **kwargs):
            if Path(os.fsdecode(path)).name == self.library.name:
                raise PermissionError('native library is busy')
            return original_unlink(path, *args, **kwargs)
        with mock.patch('os.unlink', side_effect=deny_library) as patched_unlink:
            with mock.patch.object(os, 'supports_dir_fd', os.supports_dir_fd | {patched_unlink}):
                self.assertNotEqual(self.execute(), 0)
        self.assertTrue(self.library.exists())
        self.assertTrue((self.release / '.stlmc-install.json').exists())
        if self.active.exists():
            self.assertTrue(Path(json.loads(self.active.read_text())['library']).is_file())
        self.execute()
        self.assertFalse(self.library.exists())

    def test_cli_without_selection_does_not_mutate_anything(self):
        with mock.patch('sys.stderr', new=io.StringIO()):
            with self.assertRaises(SystemExit):
                installer.main(['uninstall'])
        self.process_mock.assert_not_called()
        self.assertTrue(self.active.exists())
        self.assertTrue(self.library.exists())

    def test_directory_cleanup_permission_failure_is_not_reported_as_success(self):
        with mock.patch('os.rmdir', side_effect=PermissionError('directory is not writable')):
            status = self.execute()
        self.assertNotEqual(status, 0)

    def test_dreal_receipt_only_removes_its_binary_not_user_outputs(self):
        folder = self.solvers / 'dReal3'
        folder.mkdir(parents=True)
        executable = folder / 'dReal'
        executable.write_bytes(b'owned dReal fixture')
        install_receipts.write_dreal_receipt(executable, executable)
        output = folder / 'user.counterexample'
        output.write_bytes(b'user output')
        model = folder / 'user.model'
        model.write_text('user model')
        self.execute(solvers=('dreal',))
        self.assertFalse(executable.exists())
        self.assertEqual(output.read_bytes(), b'user output')
        self.assertEqual(model.read_text(), 'user model')

    def test_external_path_dreal_and_broad_manifest_prefix_are_preserved(self):
        external = self.root / 'system bin'
        external.mkdir()
        executable = external / 'dReal'
        executable.write_bytes(b'external executable')
        os.environ['PATH'] = str(external) + os.pathsep + os.environ.get('PATH', '')
        sentinel = self.root / 'important.txt'
        sentinel.write_text('outside managed directories')
        self.active.write_text(json.dumps({'library': str(sentinel), 'prefix': str(self.root)}))
        self.execute(solvers=('yices', 'dreal'))
        self.assertEqual(executable.read_bytes(), b'external executable')
        self.assertEqual(sentinel.read_text(), 'outside managed directories')


if __name__ == '__main__':
    unittest.main()
