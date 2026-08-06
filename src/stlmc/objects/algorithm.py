import asyncio
import os
import signal
import subprocess
import threading
from abc import abstractmethod
from queue import Empty, Queue
from typing import Dict, Set

from ..constraints.constraints import *
from ..objects.configuration import Configuration
from ..objects.goal import Goal
from ..objects.model import Model
from ..solver.abstract_solver import SMTSolver, ParallelSMTSolver
from ..util.logger import Logger
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
    def wait_and_check_sat(self):
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
            # print(result)
            if result == "False":
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
        print(f"workers={max_procs}")
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


    def set_debug(self, msg: str):
        self.debug_name = msg

    def increase_counter(self):
        self.number += 1

    def run(self, solver: ParallelSMTSolver, const: Formula):
        assert isinstance(solver, ParallelSMTSolver)

        solver.set_file_name(self.debug_name)

        self.sema.acquire()
        try:
            proc = solver.process(self.main_queue, self.sema, const)
        except Exception:
            self.sema.release()
            raise
        self.procs.add(proc)


    def kill_all(self):
        procs = list(self.procs)
        self.procs.clear()

        thread_workers = [proc for proc in procs if getattr(proc, "_stlmc_thread_worker", False)]
        process_workers = [proc for proc in procs if not getattr(proc, "_stlmc_thread_worker", False)]

        for worker in thread_workers:
            worker.terminate()

        for proc in process_workers:
            if proc.poll() is None:
                try:
                    if getattr(proc, "_stlmc_process_group", False):
                        os.killpg(proc.pid, signal.SIGTERM)
                    else:
                        proc.terminate()
                except ProcessLookupError:
                    pass

        for proc in process_workers:
            try:
                proc.wait(timeout=1)
            except subprocess.TimeoutExpired:
                try:
                    if getattr(proc, "_stlmc_process_group", False):
                        os.killpg(proc.pid, signal.SIGKILL)
                    else:
                        proc.kill()
                except ProcessLookupError:
                    pass
                proc.wait()

        for proc in process_workers:
            worker = getattr(proc, "_stlmc_worker", None)
            if worker is not None and worker is not threading.current_thread():
                worker.join(timeout=1)

        while True:
            try:
                self.main_queue.get_nowait()
            except Empty:
                break

    def wait_and_check_sat(self):
        while len(self.procs) > 0:
            try:
                result, model, proc_id = self._unpack_result(self.main_queue.get())
            except Empty:
                raise NotSupportedError("wait and check failed")
            else:
                self.increase_counter()
                if result == "False":
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

    def set_debug(self, msg: str):
        self.debug_name = msg

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

    def wait_and_check_sat(self):
        return False, None
