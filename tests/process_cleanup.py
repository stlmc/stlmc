import subprocess
import sys
import unittest
from unittest import mock
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.execution.runner import ParallelAlgRunner
from stlmc.execution.progress import ProgressTracker
from stlmc.solver.abstract_solver import JobSolver, SolveResult, SolverJob, ThreadWorker


class FakeClock:
    def __init__(self):
        self.now = 0.0

    def monotonic(self):
        return self.now

    def advance(self, seconds):
        self.now += seconds


class SlowProcess:
    def __init__(self, pid, clock=None):
        self.pid = pid
        self.clock = clock
        self.terminated = False
        self.killed = False
        self.process_group = False
        self.worker_kind = "process"
        self.completion_worker = None

    def poll(self):
        return -9 if self.killed else None

    def terminate(self):
        self.terminated = True

    def kill(self):
        self.killed = True

    def wait(self, timeout=None):
        if self.killed:
            return -9
        if timeout:
            if self.clock is not None:
                self.clock.advance(timeout)
        raise subprocess.TimeoutExpired("fake solver", timeout)


class FinishedProcess:
    def __init__(self, scenario_count):
        self.scenario = "0-{}".format(scenario_count - 1)
        self.scenario_count = scenario_count
        self.worker_kind = "process"
        self.process_group = False
        self.completion_worker = None

    def poll(self):
        return 0


class JoinWorker:
    def __init__(self):
        self.exitcode = None
        self.terminated = False

    def is_alive(self):
        return self.exitcode is None

    def join(self, timeout=None):
        self.exitcode = 0

    def terminate(self):
        self.terminated = True
        self.exitcode = -15


class ParallelRunnerCleanupTest(unittest.TestCase):
    def test_sequential_solve_interrupt_reaps_its_worker(self):
        from stlmc.utils.interrupt import (
            StlmcInterrupted, clear_interrupt, request_interrupt,
        )
        worker = SlowProcess(100)
        job = SolverJob()
        job.set_worker(worker)

        class Solver(JobSolver):
            def submit(self, const, **kwargs):
                return job

        def interrupted_wait(timeout):
            request_interrupt()
            raise TimeoutError()

        try:
            with mock.patch.object(job, 'result', side_effect=interrupted_wait):
                with self.assertRaises(StlmcInterrupted):
                    Solver().solve(object())
            self.assertTrue(worker.terminated)
            self.assertTrue(worker.killed)
        finally:
            clear_interrupt()

    def test_sequential_timeout_reaps_its_worker(self):
        worker = SlowProcess(100)
        job = SolverJob()
        job.set_worker(worker)

        class Solver(JobSolver):
            def submit(self, const, **kwargs):
                return job

        result = Solver().solve(object(), timeout=0)
        self.assertEqual(result.result, 'Unknown')
        self.assertTrue(worker.killed)

    def test_cli_sigterm_interrupts_sequential_wait_without_orphan(self):
        import os
        import select
        import signal
        code = '''
import subprocess, sys
from unittest.mock import patch
from stlmc.cli.mc import main
from stlmc.solver.abstract_solver import JobSolver, SolverJob
class Solver(JobSolver):
    def submit(self, const, **kwargs):
        worker = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])
        job = SolverJob()
        job.set_worker(worker)
        print(worker.pid, flush=True)
        return job
def run(*args):
    Solver().solve(object())
sys.argv = ['stlmc', sys.argv[1]]
with patch('stlmc.update_check.notify_if_outdated'), patch(
        'stlmc.application.workflow.VerificationWorkflow.run', side_effect=run):
    raise SystemExit(main())
'''
        env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
        process = subprocess.Popen([sys.executable, '-u', '-c', code, __file__],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
        worker_pid = None
        try:
            self.assertTrue(select.select([process.stdout], [], [], 15)[0])
            worker_pid = int(process.stdout.readline().strip())
            process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=10)
            self.assertEqual(process.returncode, 130, stdout + stderr)
            self.assertIn('execution interrupted', stdout)
            self.assertNotIn('interrupted by user', stdout)
            self.assertNotIn('Traceback', stdout + stderr)
            with self.assertRaises(ProcessLookupError):
                os.kill(worker_pid, 0)
        finally:
            if process.poll() is None:
                process.kill()
            process.communicate()
            if worker_pid is not None:
                try:
                    os.kill(worker_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass

    def test_progress_tracker_keeps_scenario_and_job_units_separate(self):
        progress = ProgressTracker()
        progress.scenario_generated(5)
        progress.job_submitted(5)
        progress.job_completed(5)

        self.assertEqual(progress.snapshot(active_workers=2), {
            "generated": 5,
            "submitted": 5,
            "completed": 5,
            "pending": 0,
            "submitted_jobs": 1,
            "completed_jobs": 1,
            "active_workers": 2,
        })

    def test_solver_job_result_honors_timeout(self):
        job = SolverJob()
        with self.assertRaises(TimeoutError):
            job.result(timeout=0)

    def test_solver_job_normalizes_multiprocessing_worker(self):
        worker = JoinWorker()
        job = SolverJob()
        job.set_worker(worker)
        self.assertIsNone(job.poll())
        self.assertEqual(job.wait(timeout=0.1), 0)
        self.assertEqual(job.poll(), 0)

    def test_thread_worker_exposes_process_compatible_liveness(self):
        worker = ThreadWorker()
        self.assertTrue(worker.is_alive())
        worker.finish()
        self.assertFalse(worker.is_alive())

    def test_completed_batch_counts_all_scenarios(self):
        runner = ParallelAlgRunner(25)
        runner.generated_scenarios = 5
        runner.submitted_scenarios = 5
        runner.submitted_jobs = 1
        worker = FinishedProcess(5)
        runner.procs.add(worker)
        runner.main_queue.put((
            SolveResult("True", None, elapsed=0.1), worker
        ))

        self.assertEqual(runner.check_sat(), (False, None))
        self.assertEqual(runner.completed_scenarios, 5)
        self.assertEqual(runner.completed_jobs, 1)
        self.assertEqual(runner.progress_snapshot()["pending"], 0)

    def test_pending_batch_is_reported_in_scenario_units(self):
        runner = ParallelAlgRunner(25)
        runner.generated_scenarios = 10
        runner.submitted_scenarios = 10
        runner.submitted_jobs = 2
        first = FinishedProcess(5)
        second = FinishedProcess(5)
        runner.procs.update((first, second))
        runner.main_queue.put(("True", None, id(first), 0.1, None))

        self.assertEqual(runner.check_sat(), (False, None))
        snapshot = runner.progress_snapshot()
        self.assertEqual(snapshot["completed"], 5)
        self.assertEqual(snapshot["pending"], 5)
        self.assertEqual(snapshot["completed_jobs"], 1)
        self.assertEqual(snapshot["submitted_jobs"], 2)

    def test_cleanup_uses_one_deadline_for_all_workers(self):
        runner = ParallelAlgRunner(4)
        runner.cleanup_timeout = 0.05
        clock = FakeClock()
        workers = [SlowProcess(pid, clock) for pid in range(100, 104)]
        runner.procs.update(workers)

        with mock.patch(
            "stlmc.execution.cleanup.time.monotonic",
            side_effect=clock.monotonic,
        ):
            runner.kill_all()

        self.assertAlmostEqual(clock.now, runner.cleanup_timeout)
        self.assertFalse(runner.procs)
        self.assertTrue(all(worker.terminated for worker in workers))
        self.assertTrue(all(worker.killed for worker in workers))

    def test_cleanup_falls_back_when_process_group_signal_is_denied(self):
        runner = ParallelAlgRunner(1)
        runner.cleanup_timeout = 0
        worker = SlowProcess(100)
        worker.process_group = True
        runner.procs.add(worker)

        with mock.patch(
            "stlmc.execution.cleanup.os.killpg",
            side_effect=PermissionError(1, "Operation not permitted"),
        ):
            runner.kill_all()

        self.assertTrue(worker.terminated)
        self.assertTrue(worker.killed)
        self.assertFalse(runner.procs)


if __name__ == "__main__":
    unittest.main()
