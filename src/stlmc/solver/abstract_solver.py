import abc
import subprocess
import threading
import time
from dataclasses import dataclass
from enum import Enum
from abc import ABC

from ..objects.configuration import Configuration


class SolverStatus(Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"

    @classmethod
    def from_legacy(cls, value):
        if isinstance(value, cls):
            return value
        return {
            "False": cls.SAT,
            "True": cls.UNSAT,
            "Unknown": cls.UNKNOWN,
            "sat": cls.SAT,
            "unsat": cls.UNSAT,
            "unknown": cls.UNKNOWN,
        }.get(value, cls.UNKNOWN)


@dataclass(frozen=True, init=False)
class SolveResult:
    """Backend-neutral result produced by a submitted solver job.

    ``status`` is canonical. The constructor accepts historical truth-valued
    strings and ``result`` exposes them for integrations using the old API.
    """

    status: SolverStatus
    assignment: object
    elapsed: float = 0.0
    error: str = None
    size: int = 0

    def __init__(self, status, assignment, elapsed=0.0, error=None, size=0):
        object.__setattr__(self, "status", SolverStatus.from_legacy(status))
        object.__setattr__(self, "assignment", assignment)
        object.__setattr__(self, "elapsed", elapsed)
        object.__setattr__(self, "error", error)
        object.__setattr__(self, "size", size)

    @property
    def result(self):
        """Historical truth-valued result retained as a compatibility view."""
        return {
            SolverStatus.SAT: "False",
            SolverStatus.UNSAT: "True",
            SolverStatus.UNKNOWN: "Unknown",
        }[self.status]


class SolverJob:
    """A cancellable solver submission shared by sequential and parallel use."""

    def __init__(self, on_complete=None):
        self._done = threading.Event()
        self._result = None
        self._worker = None
        self._on_complete = on_complete
        self.worker_kind = "process"
        self.process_group = False
        self.completion_worker = None
        self.scenario = None
        self.scenario_count = 1

    def set_worker(self, worker, *, kind="process", process_group=False,
                   completion_worker=None):
        self._worker = worker
        self.worker_kind = kind
        self.process_group = process_group
        self.completion_worker = completion_worker

    @property
    def pid(self):
        return getattr(self._worker, "pid", None)

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
        if not self._done.wait(timeout):
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

class IncrementalFormulaSolver(ABC):
    """Backend-neutral incremental solver over STLmc Formula objects.

    Track IDs are unique within active scopes; reuse after pop is allowed.
    Models expose active formula variables and exact eval values, not private
    guards. fork() copies active assertions and tracks into a new flat scope.
    Native model handles are intended for use before the next solver mutation.
    """

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
        self._thread = None

    def start(self, target):
        self._thread = threading.Thread(target=target, daemon=True)
        self._thread.start()

    def finish(self):
        self._done.set()

    def poll(self):
        return 0 if self._done.is_set() else None

    def is_alive(self):
        return not self._done.is_set()

    def terminate(self):
        # Python threads cannot be forcefully stopped; retain this process-like
        # method so SolverJob can handle thread and process workers uniformly.
        pass

    def kill(self):
        self.terminate()

    def wait(self, timeout=None):
        if not self._done.wait(timeout):
            raise subprocess.TimeoutExpired("SMT worker", timeout)
        return 0


class JobSolver(ABC):
    """Solver whose single execution primitive is a cancellable job."""

    def __init__(self, config=None):
        self.config = config if config is not None else Configuration()

    def solve(self, all_consts=None, timeout=None, query_name=""):
        if all_consts is None:
            raise ValueError("solve requires a formula")
        job = self.submit(all_consts, query_name=query_name)
        from ..utils.interrupt import raise_if_interrupted
        from ..execution.cleanup import terminate_workers
        deadline = None if timeout is None else time.monotonic() + timeout
        try:
            while True:
                raise_if_interrupted()
                remaining = None if deadline is None else max(0, deadline-time.monotonic())
                try:
                    result = job.result(0.1 if remaining is None else min(0.1, remaining))
                    raise_if_interrupted()
                    return result
                except TimeoutError:
                    if deadline is not None and time.monotonic() >= deadline:
                        terminate_workers([job], 0)
                        return SolveResult("Unknown", None, error="solver job timed out")
        except BaseException:
            terminate_workers([job], 3)
            raise

    @abc.abstractmethod
    def submit(self, const, on_complete=None, query_name=""):
        """Start a solve and call ``on_complete(result, worker)`` exactly once."""
        pass
