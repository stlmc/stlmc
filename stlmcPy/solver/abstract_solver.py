import abc
from abc import ABC

from stlmcPy.util.logger import Logger


# all solver have logger
class BaseSolver:
    def __init__(self):
        self.logger = None
        self._optimize_dict = dict()
        self.conf_dict = dict()

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

    def set_config(self, config: dict):
        self.conf_dict = config


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


class OdeSolver(BaseSolver, ABC):
    pass

# class BaseSolverFactory:
#     @abc.abstractmethod
#     def generate_solver(self):
#         pass
