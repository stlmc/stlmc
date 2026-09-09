import signal
import threading
from abc import ABC, abstractmethod
from queue import Empty, Queue
from typing import Dict, Set

from ..constraints.constraints import Formula
from ..objects.configuration import Configuration
from ..objects.goal import Goal
from ..objects.model import Model
from ..solver.abstract_solver import JobSolver, SolveResult, SolverStatus
from ..utils.interrupt import raise_if_interrupted
from ..utils.print import Printer
from .cleanup import terminate_workers
from .progress import ProgressTracker


class Algorithm(ABC):
    @abstractmethod
    def run(self, model: Model, goal: Goal, prop_dict: Dict, config: Configuration,
            solver: JobSolver, printer: Printer):
        pass

    @abstractmethod
    def set_debug(self, msg: str):
        pass


class AlgorithmRunner(ABC):
    def __init__(self):
        self.progress = ProgressTracker()

    @abstractmethod
    def run(self, solver: JobSolver, const: Formula):
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

    def reset_progress(self):
        self.progress.reset()

    def record_scenario_generated(self):
        self.progress.scenario_generated()

    def progress_snapshot(self):
        return self.progress.snapshot(self.active_workers())

    @property
    def generated_scenarios(self):
        return self.progress.generated_scenarios

    @generated_scenarios.setter
    def generated_scenarios(self, value):
        self.progress.generated_scenarios = value

    @property
    def submitted_scenarios(self):
        return self.progress.submitted_scenarios

    @submitted_scenarios.setter
    def submitted_scenarios(self, value):
        self.progress.submitted_scenarios = value

    @property
    def completed_scenarios(self):
        return self.progress.completed_scenarios

    @completed_scenarios.setter
    def completed_scenarios(self, value):
        self.progress.completed_scenarios = value

    @property
    def submitted_jobs(self):
        return self.progress.submitted_jobs

    @submitted_jobs.setter
    def submitted_jobs(self, value):
        self.progress.submitted_jobs = value

    @property
    def completed_jobs(self):
        return self.progress.completed_jobs

    @completed_jobs.setter
    def completed_jobs(self, value):
        self.progress.completed_jobs = value


class ParallelAlgRunner(AlgorithmRunner):
    def _scenario_for_process(self, proc_id):
        for proc in self.procs:
            if id(proc) == proc_id:
                return proc.scenario
        return None

    def _scenario_count_for_process(self, proc_id):
        for proc in self.procs:
            if id(proc) == proc_id:
                return proc.scenario_count
        return 1

    def _unpack_result(self, message):
        if len(message) == 2 and isinstance(message[0], SolveResult):
            solve_result, worker = message
            result = solve_result.status
            model = solve_result.assignment
            proc_id = id(worker)
            metadata = [solve_result.elapsed, solve_result.error]
        else:
            # Compatibility with queued results from older/custom workers.
            result, model, proc_id, *metadata = message
            result = SolverStatus.from_legacy(result)
        self.progress.job_completed(
            self._scenario_count_for_process(proc_id)
        )
        if len(metadata) > 0:
            self.time += metadata[0]
        if len(metadata) > 1 and metadata[1]:
            self.unknown_errors.append(metadata[1])
        return result, model, proc_id

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
            if result == SolverStatus.SAT:
                self.winning_scenario = scenario
                self.kill_all()
                return True, model
            else:
                if result == SolverStatus.UNKNOWN:
                    self.had_unknown = True
                procs = self.procs.copy()
                for proc in procs:
                    if id(proc) == proc_id:
                        self.procs.discard(proc)
                return False, None

    def __init__(self, max_procs: int):
        super().__init__()
        assert max_procs > 0
        self.procs: Set[object] = set()
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
        self.current_scenario_count = 1
        self.reset_progress()


    def set_debug(self, msg: str):
        self.debug_name = msg

    def set_scenario(self, scenario, scenario_count=1):
        self.current_scenario = scenario
        self.current_scenario_count = scenario_count

    def active_workers(self):
        return sum(proc.poll() is None for proc in self.procs)

    def increase_counter(self):
        self.number += 1

    def run(self, solver: JobSolver, const: Formula):
        assert isinstance(solver, JobSolver)

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
                def completed(solve_result, job):
                    try:
                        self.main_queue.put((solve_result, job))
                    finally:
                        self.sema.release()

                proc = solver.submit(
                    const, on_complete=completed, query_name=self.debug_name
                )
            except Exception:
                self.sema.release()
                raise
            proc.scenario = self.current_scenario
            proc.scenario_count = self.current_scenario_count
            self.procs.add(proc)
            self.progress.job_submitted(self.current_scenario_count)
        finally:
            if previous_mask is not None:
                signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)


    def kill_all(self):
        stopped_workers = terminate_workers(self.procs, self.cleanup_timeout)

        while True:
            try:
                self.main_queue.get_nowait()
            except Empty:
                break
        self.procs.difference_update(stopped_workers)

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
                if result == SolverStatus.SAT:
                    self.winning_scenario = scenario
                    if progress is not None:
                        progress(self.number)
                    self.kill_all()
                    return True, model
                else:
                    if result == SolverStatus.UNKNOWN:
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
        solve_result = self.solver.solve(
            self.const, query_name=self.debug_name
        )
        is_true = solve_result.status is SolverStatus.SAT
        self.had_unknown = self.had_unknown or solve_result.status is SolverStatus.UNKNOWN

        model = None
        if is_true:
            model = solve_result.assignment
            self.winning_scenario = self.current_scenario
        self.time = solve_result.elapsed
        self.solver = None
        self.const = None
        self.number = 0
        self.progress.job_completed(self.current_scenario_count)
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
        self.current_scenario_count = 1
        self.reset_progress()

    def set_debug(self, msg: str):
        self.debug_name = msg

    def set_scenario(self, scenario, scenario_count=1):
        self.current_scenario = scenario
        self.current_scenario_count = scenario_count

    def active_workers(self):
        return int(self.solver is not None)

    def increase_counter(self):
        self.number += 1

    def run(self, solver: JobSolver, const: Formula):
        assert isinstance(solver, JobSolver)

        self.solver = solver
        self.const = const
        self.progress.job_submitted(self.current_scenario_count)

    def kill_all(self):
        pass

    def wait_and_check_sat(self, progress=None):
        return False, None
