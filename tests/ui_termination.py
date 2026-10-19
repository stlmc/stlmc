"""Termination causes are recorded before signals and survive stop/timeout races."""
import asyncio
import importlib
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))


class UiTerminationTest(unittest.TestCase):
    def setUp(self):
        try:
            self.api = importlib.import_module('stlmc.ui.app')
        except ImportError as error:
            self.skipTest('Optional UI dependencies unavailable: ' + str(error))
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.folder = Path(temporary.name)
        for name, value in [('RUNS', self.folder), ('JOBS', {}), ('ACTIVE', None)]:
            patch = mock.patch.object(self.api, name, value)
            patch.start()
            self.addCleanup(patch.stop)
        self.job = dict(id='a' * 32, state='running', started=1, finished=None,
                        exit_code=None, termination_reason=None, request={'timeout': 120})
        (self.folder / self.job['id']).mkdir()
        self.api.JOBS[self.job['id']] = self.job
        self.api.ACTIVE = self.job['id']
        self.process = mock.Mock(returncode=130)
        self.job['_process'] = self.process
        self.stream = io.BytesIO()
        self.addCleanup(self.stream.close)

    def saved(self):
        return json.loads((self.folder / self.job['id'] / 'job.json').read_text())

    def test_timeout_is_saved_before_signal_and_not_overwritten_by_late_stop(self):
        self.process.wait.side_effect = subprocess.TimeoutExpired('worker', 120)

        def cleanup(process):
            saved = self.saved()
            self.assertEqual(saved['state'], 'stopping')
            self.assertEqual(saved['termination_reason'], 'timeout')
            self.assertIn('termination_requested_at', saved)
            self.api.stop(self.job['id'])
            self.assertEqual(self.job['termination_reason'], 'timeout')

        with mock.patch.object(self.api, 'stop_group', side_effect=cleanup), \
                mock.patch.object(self.api.threading, 'Thread') as thread:
            self.api.watch(self.job, self.process, self.stream)
        thread.assert_not_called()
        self.assertEqual(self.saved()['state'], 'timed_out')
        self.assertEqual(self.saved()['exit_code'], 130)
        self.assertTrue(self.stream.closed)
        self.assertIsNone(self.api.ACTIVE)

    def test_user_stop_is_saved_before_cleanup_thread_starts(self):
        with mock.patch.object(self.api.threading, 'Thread') as thread:
            thread.return_value.start.side_effect = lambda: self.assertEqual(
                self.saved()['termination_reason'], 'user_stop')
            self.api.stop(self.job['id'])
        self.assertEqual(self.saved()['state'], 'stopping')
        with mock.patch.object(self.api, 'stop_group'):
            self.api.watch(self.job, self.process, self.stream)
        self.assertEqual(self.saved()['state'], 'cancelled')
        self.assertEqual(self.saved()['termination_reason'], 'user_stop')

    def test_stop_requested_first_wins_even_if_wait_also_times_out(self):
        self.api.request_termination(self.job, 'user_stop')
        self.process.wait.side_effect = subprocess.TimeoutExpired('worker', 120)
        with mock.patch.object(self.api, 'stop_group'):
            self.api.watch(self.job, self.process, self.stream)
        self.assertEqual(self.saved()['state'], 'cancelled')
        self.assertEqual(self.saved()['termination_reason'], 'user_stop')

    def test_first_reason_and_request_timestamp_are_immutable(self):
        with mock.patch.object(self.api.time, 'time', return_value=123):
            self.assertTrue(self.api.request_termination(self.job, 'timeout'))
        self.assertFalse(self.api.request_termination(self.job, 'server_shutdown'))
        self.assertFalse(self.api.request_termination(self.job, 'user_stop'))
        self.assertEqual(self.saved()['termination_requested_at'], 123)
        self.assertEqual(self.saved()['termination_reason'], 'timeout')

    def test_server_shutdown_is_not_misclassified_as_user_stop(self):
        async def shutdown():
            async with self.api.lifespan(None):
                pass

        def cleanup(process):
            self.assertEqual(self.saved()['termination_reason'], 'server_shutdown')

        with mock.patch.object(self.api, 'stop_group', side_effect=cleanup):
            asyncio.run(shutdown())
            self.api.watch(self.job, self.process, self.stream)
        self.assertEqual(self.saved()['state'], 'interrupted')
        self.assertEqual(self.saved()['termination_reason'], 'server_shutdown')

    def test_simultaneous_stop_and_timeout_record_one_consistent_cause(self):
        barrier = threading.Barrier(3)
        outcomes = []

        def request(reason):
            barrier.wait(timeout=5)
            claimed = self.api.request_termination(self.job, reason)
            outcomes.append((reason, claimed))

        workers = [threading.Thread(target=request, args=(reason,))
                   for reason in ('user_stop', 'timeout')]
        for worker in workers:
            worker.start()
        barrier.wait(timeout=5)
        for worker in workers:
            worker.join(timeout=5)
            self.assertFalse(worker.is_alive())
        winners = [reason for reason, claimed in outcomes if claimed]
        self.assertEqual(len(winners), 1)
        self.assertEqual(self.saved()['termination_reason'], winners[0])
        with mock.patch.object(self.api, 'stop_group'):
            self.api.watch(self.job, self.process, self.stream)
        self.assertEqual(self.saved()['state'],
                         'timed_out' if winners[0] == 'timeout' else 'cancelled')

    def test_normal_completion_and_failure_keep_their_status(self):
        for code, expected in [(0, 'completed'), (2, 'failed'), (130, 'interrupted'),
                               (-signal.SIGTERM, 'interrupted')]:
            with self.subTest(code=code):
                self.job.update(state='running', termination_reason=None)
                self.process.returncode = code
                with mock.patch.object(self.api, 'stop_group') as cleanup:
                    self.api.watch(self.job, self.process, io.BytesIO())
                cleanup.assert_not_called()
                self.assertEqual(self.saved()['state'], expected)
                self.assertIsNone(self.saved()['termination_reason'])
                self.assertFalse(self.api.request_termination(self.job, 'user_stop'))

    def test_recorded_reason_survives_reloading_and_old_metadata_is_not_rewritten(self):
        self.api.request_termination(self.job, 'timeout')
        self.api.JOBS.clear()
        self.assertEqual(self.api.load_job(self.job['id'])['termination_reason'], 'timeout')
        self.assertEqual(self.saved()['state'], 'stopping')
        path = self.folder / self.job['id'] / 'job.json'
        path.write_text(json.dumps({'id': self.job['id'], 'state': 'timed_out', 'started': 1}))
        original = path.read_bytes()
        loaded = self.api.load_job(self.job['id'])
        self.assertNotIn('termination_reason', loaded)
        self.assertEqual(path.read_bytes(), original)

    @unittest.skipUnless(os.name == 'posix', 'Dedicated process groups require POSIX')
    def test_real_timeout_stops_process_and_persists_reason(self):
        self.job['request']['timeout'] = .2
        process = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'],
                                   start_new_session=True, stdout=subprocess.DEVNULL,
                                   stderr=subprocess.DEVNULL)
        self.job['_process'] = process
        try:
            self.api.watch(self.job, process, self.stream)
            self.assertIsNotNone(process.poll())
            self.assertEqual(self.saved()['state'], 'timed_out')
            self.assertEqual(self.saved()['termination_reason'], 'timeout')
        finally:
            if process.poll() is None:
                self.api.stop_group(process)


if __name__ == '__main__':
    unittest.main()
