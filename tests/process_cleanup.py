import subprocess
import sys
import unittest
from unittest import mock
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.objects.algorithm import ParallelAlgRunner
from stlmc.solver.abstract_solver import SolveResult, SolverJob, ThreadWorker


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
            "stlmc.objects.algorithm.time.monotonic",
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
            "stlmc.objects.algorithm.os.killpg",
            side_effect=PermissionError(1, "Operation not permitted"),
        ):
            runner.kill_all()

        self.assertTrue(worker.terminated)
        self.assertTrue(worker.killed)
        self.assertFalse(runner.procs)


if __name__ == "__main__":
    unittest.main()
