"""Diagnostic helpers must not change benchmark inputs or hide failures."""
import importlib.util
from pathlib import Path
import signal
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location('diagnostics',
    Path(__file__).resolve().parents[1] / 'tools/diagnose_ci_benchmarks.py')
TOOL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOL)


class CiBenchmarkDiagnosticTest(unittest.TestCase):
    def test_process_snapshot_parses_only_safe_columns_and_selects_descendants(self):
        rows = TOOL.parse_processes('10 1 25.5 1024 stlmc\n11 10 80 2048 dReal\n12 1 4 128 unrelated\n')
        self.assertEqual([row['pid'] for row in TOOL.process_tree(rows, 10)], [10, 11])
        self.assertEqual(set(rows[0]), {'pid', 'ppid', 'pcpu', 'rss_kib', 'comm'})

    def test_cpu_percent_uses_one_core_basis(self):
        before = SimpleNamespace(ru_utime=1, ru_stime=2)
        after = SimpleNamespace(ru_utime=4, ru_stime=3)
        self.assertEqual(TOOL.cpu_summary(before, after, 2)['average_cpu_percent_one_core'], 200)

    def test_timeout_requests_stlmc_cleanup_before_forced_kill(self):
        process = mock.Mock(pid=123)
        process.poll.return_value = None
        process.wait.side_effect = [subprocess.TimeoutExpired('stlmc', 10), 0]
        with mock.patch.object(TOOL.os, 'killpg') as kill:
            TOOL.stop_process(process)
        self.assertEqual(kill.call_args_list,
                         [mock.call(123, signal.SIGINT), mock.call(123, signal.SIGKILL)])

    def test_completed_process_is_never_signalled(self):
        process = mock.Mock()
        process.poll.return_value = 0
        with mock.patch.object(TOOL.os, 'killpg') as kill:
            TOOL.stop_process(process)
        kill.assert_not_called()

    def test_expected_status_parser_and_fixed_case_selection(self):
        self.assertEqual(TOOL.RESULT.search('status : violated at bound 3').groups(), ('violated', '3'))
        self.assertEqual([case[3] for case in TOOL.CASES], [3, 2, 1])
        self.assertEqual(len(TOOL.CASES), 3)

    def test_file_inventory_hashes_exact_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'query.smt2'
            path.write_bytes(b'abc')
            info = TOOL.file_info(path)
        self.assertEqual(info['size'], 3)
        self.assertEqual(info['sha256'], 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad')


if __name__ == '__main__':
    unittest.main()
