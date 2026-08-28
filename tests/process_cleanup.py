import subprocess
import sys
import unittest
from unittest import mock
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.objects.algorithm import ParallelAlgRunner


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
        self._stlmc_process_group = False

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
        self._stlmc_scenario = "0-{}".format(scenario_count - 1)
        self._stlmc_scenario_count = scenario_count

    def poll(self):
        return 0


class ParallelRunnerCleanupTest(unittest.TestCase):
    def test_completed_batch_counts_all_scenarios(self):
        runner = ParallelAlgRunner(25)
        runner.generated_scenarios = 5
        runner.submitted_scenarios = 5
        runner.submitted_jobs = 1
        worker = FinishedProcess(5)
        runner.procs.add(worker)
        runner.main_queue.put(("True", None, id(worker), 0.1, None))

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
        worker._stlmc_process_group = True
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
