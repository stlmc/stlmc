import abc
import subprocess
from abc import ABC
from queue import Queue
from threading import Semaphore

from ..util.logger import Logger

# all solver have logger
from ..objects.configuration import Configuration


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
    def process(self, main_queue: Queue, sema: Semaphore, const):
        pass


class OdeSolver(BaseSolver, ABC):
    pass
