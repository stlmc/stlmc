import abc
from abc import ABC

from stlmcPy.util.logger import Logger

# all solver have logger
class BaseSolver(Logger):

    @abc.abstractmethod
    def solve(self, all_consts=None, cont_vars_dict=None, boolean_abstract_dict=None):
        pass

    @abc.abstractmethod
    def make_assignment(self):
        pass


class SMTSolver:
    @abc.abstractmethod
    def simplify(self, consts):
        pass

    @abc.abstractmethod
    def substitution(self, const, *dicts):
        pass

    @abc.abstractmethod
    def add(self, const):
        pass


# class OdeSolver(BaseSolver):
#     pass
