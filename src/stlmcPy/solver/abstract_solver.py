import abc
from abc import ABC

from ..constraints.constraints import Formula
# all solver have logger
from ..objects.configuration import Configuration


class BaseSolver:
    pass


class SMTSolver(BaseSolver):
    sat = "sat"
    unsat = "unsat"
    unknown = "unknown"

    @abc.abstractmethod
    def check_sat(self, *assumption, **information):
        pass

    @abc.abstractmethod
    def make_assignment(self):
        pass

    @abc.abstractmethod
    def push(self):
        pass

    @abc.abstractmethod
    def pop(self):
        pass

    @abc.abstractmethod
    def reset(self):
        pass

    @abc.abstractmethod
    def add(self, formula: Formula):
        pass

    @abc.abstractmethod
    def assert_and_track(self, formula: Formula, track_id: str):
        pass

    @abc.abstractmethod
    def unsat_core(self):
        pass


class OdeSolver(BaseSolver, ABC):
    pass
