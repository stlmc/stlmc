import asyncio
import subprocess
import threading
from abc import abstractmethod
from multiprocessing import *
from queue import Empty

from ..encoding.enumerate import *
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
    def _check_sat(self):
        while True:
            try:
                result, model, smt_time = self.main_queue.get_nowait()
            except Empty:
                # no counterexample or unknown
                pass
            else:
                self.result = result
                if result == "False":
                    self.time += smt_time
                    self.model = model
                else:
                    self.model = None
                self.kill_all()
                break

    def check_sat(self):
        try:
            result, model, proc_id = self.main_queue.get_nowait()
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
                procs = self.procs.copy()
                for proc in procs:
                    if id(proc) == proc_id:
                        self.procs.discard(proc)
                return False, None

    def __init__(self, max_procs: int):
        super().__init__()
        assert max_procs > 0
        print("max procs: {}".format(max_procs))
        self.procs: Set[subprocess.Popen] = set()
        self.sema = threading.Semaphore(max_procs)
        self.time = 0.0
        self.main_queue: Queue = Queue()

        self.result = None
        self.model = None
        self.debug_name = ""
        self.number = 0


    def set_debug(self, msg: str):
        self.debug_name = msg

    def increase_counter(self):
        self.number += 1

    def run(self, solver: ParallelSMTSolver, const: Formula):
        assert isinstance(solver, ParallelSMTSolver)

        solver.set_file_name(self.debug_name)

        self.sema.acquire()
        proc = solver.process(self.main_queue, self.sema, const)
        self.procs.add(proc)


    def kill_all(self):
        for proc in self.procs:
            proc.terminate()
            proc.kill()
            proc.wait()

    def wait_and_check_sat(self):
        while len(self.procs) > 0:
            try:
                result, model, proc_id = self.main_queue.get()
            except Empty:
                raise NotSupportedError("wait and check failed")
            else:
                self.increase_counter()
                if result == "False":
                    self.kill_all()
                    return True, model
                else:
                    procs = self.procs.copy()
                    for proc in procs:
                        if id(proc) == proc_id:
                            self.procs.discard(proc)
        return False, None


class NormalRunner(AlgorithmRunner):
    def check_sat(self):
        assert self.solver is not None and self.const is not None
        result, size = self.solver.solve(self.const)
        is_true = result == "False"

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

    def set_debug(self, msg: str):
        self.debug_name = msg

    def increase_counter(self):
        self.number += 1

    def run(self, solver: ParallelSMTSolver, const: Formula):
        assert isinstance(solver, ParallelSMTSolver)

        solver.set_file_name(self.debug_name)

        self.solver = solver
        self.const = const

    def kill_all(self):
        pass

    def wait_and_check_sat(self):
        return False, None
