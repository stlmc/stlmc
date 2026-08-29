import abc
import subprocess
import threading
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


class SMTSolver(BaseSolver):
    @abc.abstractmethod
    def simplify(self, consts):
        pass

    @abc.abstractmethod
    def substitution(self, const, *dicts):
        pass

    @abc.abstractmethod
    def add(self, const):
        pass

    @abc.abstractmethod
    def set_logic(self, logic_name: str):
        pass

    @abc.abstractmethod
    def set_time_bound(self, time_bound: str):
        pass


class ParallelSMTSolver(SMTSolver):
    @abc.abstractmethod
    def submit(self, const, on_complete):
        """Start a solve and call ``on_complete(result, worker)`` exactly once."""
        pass


class OdeSolver(BaseSolver, ABC):
    pass
