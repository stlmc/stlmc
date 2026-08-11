import asyncio
import os
import signal
import subprocess
import threading
import time
from abc import abstractmethod
from queue import Empty, Queue
from typing import Dict, Set

from ..constraints.constraints import *
from ..objects.configuration import Configuration
from ..objects.goal import Goal
from ..objects.model import Model
from ..solver.abstract_solver import SMTSolver, ParallelSMTSolver
from ..util.logger import Logger
from ..util.interrupt import raise_if_interrupted
from ..util.print import Printer


class Algorithm:
    @abstractmethod
    def run(self, model: Model, goal: Goal, prop_dict: Dict, config: Configuration,
            solver: SMTSolver, logger: Logger, printer: Printer):
        pass

    @abstractmethod
    def set_debug(self, msg: str):
        pass


class AlgorithmRunner:
    @abstractmethod
    def run(self, solver: SMTSolver, const: Formula):
        pass

    @abstractmethod
    def check_sat(self):
        pass

    @abstractmethod
    def wait_and_check_sat(self, progress=None):
        pass

    @abstractmethod
    def set_debug(self, msg: str):
        pass


async def solve(solver: SMTSolver, const: Formula):
    return await asyncio.wait_for(solver.solve(const), timeout=100000000.0)


def call_back(p):
    print(p)
    if p[0] == "False":
        print("not done!")
    else:
        print("done!")


class ParallelAlgRunner(AlgorithmRunner):
    def _scenario_for_process(self, proc_id):
        for proc in self.procs:
            if id(proc) == proc_id:
                return getattr(proc, "_stlmc_scenario", None)
        return None

    def _unpack_result(self, message):
        result, model, proc_id, *metadata = message
        if len(metadata) > 0:
            self.time += metadata[0]
        if len(metadata) > 1 and metadata[1]:
            self.unknown_errors.append(metadata[1])
        return result, model, proc_id

    def _check_sat(self):
        while True:
            try:
                result, model, proc_id = self._unpack_result(self.main_queue.get_nowait())
            except Empty:
                # no counterexample or unknown
                pass
            else:
                self.result = result
                if result == "False":
                    self.model = model
                else:
                    self.model = None
                self.kill_all()
                break

    def check_sat(self):
        try:
            result, model, proc_id = self._unpack_result(self.main_queue.get_nowait())
        except Empty:
            # no counterexample or unknown
            return False, None
        else:
            self.increase_counter()
            scenario = self._scenario_for_process(proc_id)
            # print(result)
            if result == "False":
                self.winning_scenario = scenario
                self.kill_all()
                return True, model
            else:
                if result == "Unknown":
                    self.had_unknown = True
                procs = self.procs.copy()
                for proc in procs:
                    if id(proc) == proc_id:
                        self.procs.discard(proc)
                return False, None

    def __init__(self, max_procs: int):
        super().__init__()
        assert max_procs > 0
        self.procs: Set[subprocess.Popen] = set()
        self.sema = threading.Semaphore(max_procs)
        self.time = 0.0
        self.main_queue: Queue = Queue()

        self.result = None
        self.model = None
        self.debug_name = ""
        self.number = 0
        self.had_unknown = False
        self.unknown_errors = []
        self.current_scenario = None
        self.winning_scenario = None
        self.cleanup_timeout = 3.0


    def set_debug(self, msg: str):
        self.debug_name = msg

    def set_scenario(self, scenario):
        self.current_scenario = scenario

    def increase_counter(self):
        self.number += 1

    def run(self, solver: ParallelSMTSolver, const: Formula):
        assert isinstance(solver, ParallelSMTSolver)

        solver.set_file_name(self.debug_name)

        while not self.sema.acquire(timeout=0.1):
            raise_if_interrupted()
        raise_if_interrupted()
        # A signal between spawning a solver and registering it in self.procs
        # would leave cleanup unable to find the child.  Block termination
        # signals across that small critical section; a pending signal is
        # delivered immediately after the registered process becomes visible.
        blocked_signals = {
            sig for sig in (getattr(signal, "SIGINT", None),
                            getattr(signal, "SIGTERM", None))
            if sig is not None
        }
        previous_mask = None
        if hasattr(signal, "pthread_sigmask"):
            previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, blocked_signals)
        try:
            try:
                proc = solver.process(self.main_queue, self.sema, const)
            except Exception:
                self.sema.release()
                raise
            proc._stlmc_scenario = self.current_scenario
            self.procs.add(proc)
        finally:
            if previous_mask is not None:
                signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)


    def kill_all(self):
        procs = list(self.procs)

        thread_workers = [proc for proc in procs if getattr(proc, "_stlmc_thread_worker", False)]
        process_workers = [proc for proc in procs if not getattr(proc, "_stlmc_thread_worker", False)]

        for worker in thread_workers:
            worker.terminate()

        def is_running(proc):
            if hasattr(proc, "poll"):
                return proc.poll() is None
            return proc.is_alive()

        for proc in process_workers:
            if is_running(proc):
                try:
                    if getattr(proc, "_stlmc_process_group", False):
                        os.killpg(proc.pid, signal.SIGTERM)
                    else:
                        proc.terminate()
                except ProcessLookupError:
                    pass

        # Use one deadline for the whole worker set.  Waiting one second per
        # worker can exceed the outer benchmark runner's five-second grace
        # period and let it kill STLMC before child cleanup has finished.
        deadline = time.monotonic() + self.cleanup_timeout
        for proc in process_workers:
            remaining = max(0.0, deadline - time.monotonic())
            if not is_running(proc):
                continue
            if hasattr(proc, "wait"):
                try:
                    proc.wait(timeout=remaining)
                except subprocess.TimeoutExpired:
                    pass
            else:
                proc.join(timeout=remaining)

        for proc in process_workers:
            if not is_running(proc):
                continue
            try:
                if hasattr(proc, "wait"):
                    if getattr(proc, "_stlmc_process_group", False):
                        os.killpg(proc.pid, signal.SIGKILL)
                    else:
                        proc.kill()
                else:
                    proc.kill()
            except ProcessLookupError:
                pass

        for proc in process_workers:
            if hasattr(proc, "wait"):
                try:
                    proc.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    pass
            else:
                proc.join(timeout=1)

        for proc in process_workers:
            worker = getattr(proc, "_stlmc_worker", None)
            if worker is not None and worker is not threading.current_thread():
                worker.join(timeout=1)

        while True:
            try:
                self.main_queue.get_nowait()
            except Empty:
                break
        finished_processes = {
            proc for proc in process_workers if not is_running(proc)
        }
        self.procs.difference_update(thread_workers)
        self.procs.difference_update(finished_processes)

    def wait_and_check_sat(self, progress=None):
        while len(self.procs) > 0:
            try:
                message = self.main_queue.get(timeout=0.1)
            except Empty:
                raise_if_interrupted()
                continue
            else:
                result, model, proc_id = self._unpack_result(message)
                self.increase_counter()
                scenario = self._scenario_for_process(proc_id)
                if result == "False":
                    self.winning_scenario = scenario
                    if progress is not None:
                        progress(self.number)
                    self.kill_all()
                    return True, model
                else:
                    if result == "Unknown":
                        self.had_unknown = True
                    procs = self.procs.copy()
                    for proc in procs:
                        if id(proc) == proc_id:
                            self.procs.discard(proc)
                    if progress is not None:
                        progress(self.number)
        return False, None


class NormalRunner(AlgorithmRunner):
    def check_sat(self):
        assert self.solver is not None and self.const is not None
        self.solver.clear()
        result, size = self.solver.solve(self.const)
        is_true = result == "False"
        self.had_unknown = self.had_unknown or result == "Unknown"

        model = None
        if is_true:
            model = self.solver.make_assignment()
            self.winning_scenario = self.current_scenario
        self.time = self.solver.logger.get_duration_time("solving timer")
        self.solver = None
        self.const = None
        self.number = 0
        return is_true, model

    def __init__(self):
        super().__init__()
        self.time = 0.0
        self.main_queue: Queue = Queue()
        self.solver = None
        self.const = None
        self.number = 0
        self.had_unknown = False
        self.current_scenario = None
        self.winning_scenario = None

    def set_debug(self, msg: str):
        self.debug_name = msg

    def set_scenario(self, scenario):
        self.current_scenario = scenario

    def increase_counter(self):
        self.number += 1

    def run(self, solver: SMTSolver, const: Formula):
        assert isinstance(solver, SMTSolver)

        if hasattr(solver, "set_file_name"):
            solver.set_file_name(self.debug_name)

        self.solver = solver
        self.const = const

    def kill_all(self):
        pass

    def wait_and_check_sat(self, progress=None):
        return False, None
