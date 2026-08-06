import signal
import threading
import unittest
from queue import Queue
from unittest.mock import patch

from stlmc.exception.exception import NotSupportedError
from stlmc.objects.algorithm import ParallelAlgRunner
from stlmc.solver.dreal import dRealSolver
from stlmc.solver.yices import YicesSolver


class FakeProcess:
    def __init__(self, returncode=0, stdout=b"", stderr=b""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr
        self.terminated = False
        self.pid = 12345

    def communicate(self):
        return self.stdout, self.stderr

    def poll(self):
        return self.returncode

    def terminate(self):
        self.terminated = True

    def wait(self, timeout=None):
        return self.returncode

    def kill(self):
        self.returncode = -9


class ParallelRunnerTest(unittest.TestCase):
    def test_unknown_is_recorded_and_process_is_removed(self):
        runner = ParallelAlgRunner(1)
        proc = FakeProcess()
        runner.procs.add(proc)
        runner.main_queue.put(("Unknown", None, id(proc), 0.25, "parse error"))

        self.assertEqual(runner.check_sat(), (False, None))
        self.assertTrue(runner.had_unknown)
        self.assertEqual(runner.unknown_errors, ["parse error"])
        self.assertEqual(runner.time, 0.25)
        self.assertFalse(runner.procs)

    def test_kill_all_clears_processes_and_stale_results(self):
        runner = ParallelAlgRunner(1)
        proc = FakeProcess(returncode=None)
        runner.procs.add(proc)
        runner.main_queue.put(("Unknown", None, id(proc)))

        runner.kill_all()

        self.assertTrue(proc.terminated)
        self.assertFalse(runner.procs)
        self.assertTrue(runner.main_queue.empty())

    def test_kill_all_terminates_the_process_group(self):
        runner = ParallelAlgRunner(1)
        proc = FakeProcess(returncode=None)
        proc._stlmc_process_group = True
        runner.procs.add(proc)

        with patch("stlmc.objects.algorithm.os.killpg") as killpg:
            runner.kill_all()

        killpg.assert_called_once_with(proc.pid, signal.SIGTERM)
        self.assertFalse(runner.procs)

    def test_yices_parallel_fails_explicitly_and_restores_permit(self):
        runner = ParallelAlgRunner(1)

        with self.assertRaises(NotSupportedError):
            runner.run(YicesSolver(), object())

        self.assertTrue(runner.sema.acquire(blocking=False))


class DRealParallelWorkerTest(unittest.TestCase):
    def run_worker(self, proc):
        queue = Queue()
        sema = threading.Semaphore(0)
        dRealSolver().parallel_check_sat(queue, sema, proc)
        message = queue.get_nowait()
        self.assertTrue(sema.acquire(blocking=False))
        return message

    def test_unsat(self):
        self.assertEqual(self.run_worker(FakeProcess(stdout=b"unsat\n"))[0], "True")

    def test_delta_sat_model(self):
        output = b"Solution:\ncurrentMode_0 : [ ENTIRE ] = [0, 0]\n"
        self.assertEqual(self.run_worker(FakeProcess(stdout=output))[0], "False")

    def test_nonzero_exit_is_unknown(self):
        message = self.run_worker(FakeProcess(returncode=2, stderr=b"parse error"))
        self.assertEqual(message[0], "Unknown")
        self.assertIn("parse error", message[4])

    def test_worker_exception_is_unknown(self):
        proc = FakeProcess(stdout=b"\xff")
        message = self.run_worker(proc)
        self.assertEqual(message[0], "Unknown")


if __name__ == "__main__":
    unittest.main()
