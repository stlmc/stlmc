import abc
import subprocess
import threading
import time
from dataclasses import dataclass
from enum import Enum
from abc import ABC

from ..util.logger import Logger

# all solver have logger
from ..objects.configuration import Configuration


class SolverStatus(Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class SolveResult:
    """Backend-neutral result produced by a submitted solver job."""

    result: str
    assignment: object
    elapsed: float = 0.0
    error: str = None
    size: int = 0


class SolverJob:
    """A cancellable solver submission shared by sequential and parallel use."""

    def __init__(self, on_complete=None):
        self._done = threading.Event()
        self._result = None
        self._worker = None
        self._on_complete = on_complete

    def set_worker(self, worker):
        self._worker = worker

    def complete(self, result: SolveResult):
        if self._done.is_set():
            return
        self._result = result
        self._done.set()
        if self._on_complete is not None:
            self._on_complete(result, self)

    def done(self):
        return self._done.is_set()

    def result(self, timeout=None):
        deadline = None if timeout is None else time.monotonic() + timeout
        while not self._done.wait(0.1):
            if deadline is not None and time.monotonic() >= deadline:
                raise TimeoutError("solver job timed out")
        return self._result

    def poll(self):
        if self._worker is None:
            return None
        if hasattr(self._worker, "poll"):
            return self._worker.poll()
        if hasattr(self._worker, "is_alive"):
            return None if self._worker.is_alive() else getattr(
                self._worker, "exitcode", 0
            )
        return 0 if self._done.is_set() else None

    def terminate(self):
        if self._worker is not None and hasattr(self._worker, "terminate"):
            self._worker.terminate()

    def kill(self):
        if self._worker is None:
            return
        if hasattr(self._worker, "kill"):
            self._worker.kill()
        elif hasattr(self._worker, "terminate"):
            self._worker.terminate()

    def wait(self, timeout=None):
        if self._worker is None:
            return 0
        if hasattr(self._worker, "wait"):
            return self._worker.wait(timeout=timeout)
        if hasattr(self._worker, "join"):
            self._worker.join(timeout=timeout)
            if self._worker.is_alive():
                raise subprocess.TimeoutExpired("solver worker", timeout)
            return getattr(self._worker, "exitcode", 0)
        return 0

    def __getattr__(self, name):
        worker = object.__getattribute__(self, "_worker")
        if worker is None:
            raise AttributeError(name)
        return getattr(worker, name)


class IncrementalFormulaSolver(ABC):
    """Backend-neutral incremental solver over STLmc Formula objects."""

    @abc.abstractmethod
    def add(self, formula):
        pass

    @abc.abstractmethod
    def push(self):
        pass

    @abc.abstractmethod
    def pop(self):
        pass

    @abc.abstractmethod
    def check(self) -> SolverStatus:
        pass

    @abc.abstractmethod
    def model(self):
        pass

    @abc.abstractmethod
    def track(self, formula, track_id: str):
        pass

    @abc.abstractmethod
    def unsat_core(self):
        pass

    @abc.abstractmethod
    def fork(self):
        pass

class ThreadWorker:
    """Small process-like wrapper used by in-process parallel SMT workers."""

    def __init__(self):
        self._done = threading.Event()
        self._cancelled = threading.Event()
        self._thread = None
        self._stlmc_thread_worker = True

    def start(self, target):
        self._thread = threading.Thread(target=target, daemon=True)
        self._thread.start()

    def finish(self):
        self._done.set()

    @property
    def cancelled(self):
        return self._cancelled.is_set()

    def poll(self):
        return 0 if self._done.is_set() else None

    def is_alive(self):
        return not self._done.is_set()

    def terminate(self):
        self._cancelled.set()

    def kill(self):
        self.terminate()

    def wait(self, timeout=None):
        if not self._done.wait(timeout):
            raise subprocess.TimeoutExpired("SMT worker", timeout)
        return 0


class BaseSolver:
    def __init__(self):
        self.logger = None
        self._optimize_dict = dict()
        self.config = Configuration()
        self.time_dict = dict()

    def set_optimize_flag(self, name: str, value: bool):
        assert isinstance(value, bool)
        self._optimize_dict[name] = value

    def get_optimize_flag(self, name: str):
        if name in self._optimize_dict:
            return self._optimize_dict[name]
        return False

    def append_logger(self, logger: Logger):
        self.logger = logger

    @abc.abstractmethod
    def solve(self, all_consts=None, cont_vars_dict=None, boolean_abstract_dict=None):
        pass

    @abc.abstractmethod
    def make_assignment(self):
        pass

    def set_config(self, config: Configuration):
        self.config = config

    def set_time(self, keyword: str, value):
        if keyword in self.time_dict:
            self.time_dict[keyword] += value
        else:
            self.time_dict[keyword] = value

    def get_time(self, keyword: str):
        assert keyword in self.time_dict
        return self.time_dict[keyword]

    def reset_time(self, keyword: str):
        if keyword in self.time_dict:
            self.time_dict[keyword] = 0


class JobSolver(BaseSolver):
    """Solver whose single execution primitive is a cancellable job."""

    def solve(self, all_consts=None, cont_vars_dict=None,
              boolean_abstract_dict=None):
        if all_consts is None:
            raise ValueError("solve requires a formula")
        assert self.logger is not None
        self.logger.reset_timer()
        self.logger.start_timer("solving timer")
        job = self.submit(all_consts)
        timeout = getattr(self, "_solve_timeout", None)
        try:
            solve_result = job.result(timeout)
        except TimeoutError:
            job.kill()
            solve_result = SolveResult(
                "Unknown", None, error="solver job timed out"
            )
        finally:
            self.logger.stop_timer("solving timer")
        self.reset_time("solving timer")
        self.set_time("solving timer", solve_result.elapsed)
        self._last_assignment = solve_result.assignment
        return solve_result.result, solve_result.size

    @abc.abstractmethod
    def submit(self, const, on_complete=None):
        """Start a solve and call ``on_complete(result, worker)`` exactly once."""
        pass

    @abc.abstractmethod
    def clear(self):
        pass

    @abc.abstractmethod
    def set_logic(self, logic_name: str):
        pass

    @abc.abstractmethod
    def set_time_bound(self, time_bound: str):
        pass


# Backward-compatible imports for integrations written against the old names.
SMTSolver = JobSolver
ParallelSMTSolver = JobSolver


class OdeSolver(BaseSolver, ABC):
    pass
