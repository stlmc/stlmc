import os
import threading
from abc import abstractmethod
from multiprocessing import Process, Queue, active_children
from queue import Empty
from typing import Set

from ..constraints.constraints import Formula
from ..encoding.smt.model.stlmc_model import STLmcModel
from ..solver.abstract_solver import SMTSolver


class SmtSolverRunner:
    def __init__(self):
        self.log_file_name = ""

    @abstractmethod
    def run(self, solver: SMTSolver, const: Formula, model: STLmcModel):
        pass

    @abstractmethod
    def check_sat(self):
        pass

    @abstractmethod
    def wait_and_check_sat(self):
        pass


class ParallelSmtSolverRunner(SmtSolverRunner):
    def __init__(self, max_procs: int):
        super().__init__()
        assert max_procs > 0
        print("max procs: {}".format(max_procs))
        self.sema = threading.Semaphore(max_procs)
        self.time = 0.0
        self.main_queue: Queue = Queue()

        self.result = None
        self.model = None

    def run(self, solver: SMTSolver, const: Formula, model: STLmcModel):
        assert isinstance(solver, SMTSolver)
        self._make_runner(solver, const, model)

    def _make_runner(self, solver: SMTSolver, const, model):
        check_sat_proc = Process(target=self._run, args=(solver, const, model))
        # check_sat_proc.daemon = True
        check_sat_proc.start()

    def _run(self, solver: SMTSolver, const: Formula, model: STLmcModel):
        self.sema.acquire()
        result = solver.check_sat(const, model=model)
        if result == SMTSolver.sat:
            m = solver.make_assignment()
        else:
            m = None
        self.main_queue.put((result, m))
        self.sema.release()

    def check_sat(self):
        try:
            result, model = self.main_queue.get_nowait()
        except Empty:
            # no counterexample or unknown
            return SMTSolver.unknown, None
        else:
            # print(result)
            if result == SMTSolver.sat:
                self._kill_all()
            return result, model

    def wait_and_check_sat(self):
        while len(active_children()) > 0:
            try:
                result, model = self.main_queue.get_nowait()
            except Empty:
                # raise Exception("wait and check failed")
                continue
            else:
                if result == SMTSolver.sat:
                    self._kill_all()
                    return result, model
            print("current proc: {}".format(len(active_children())))
        print("end of wait and check proc : {}".format(len(active_children())))
        return SMTSolver.unsat, None

    def _kill_all(self):
        for proc in active_children():
            proc.terminate()
            proc.kill()
            proc.join()
            # proc.wait()
        self.main_queue.close()
        self.main_queue.join_thread()
