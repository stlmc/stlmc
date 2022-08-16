import abc

from ..encoding.smt.model.aux import *
from ..objects.goal import Goal
from ..objects.model import Model
from ..solver.abstract_solver import SMTSolver
from ..solver.assignment import Assignment


class Algorithm:
    @abc.abstractmethod
    def run(self, model: Model, goal: Goal, solver: SMTSolver):
        pass


class FormulaStack:
    def __init__(self):
        self._stack: List[List] = list()

    def push(self, *args):
        element = []
        for f in args:
            assert isinstance(f, Formula)
            element.append(f)
        self._stack.append(element)

    def pop(self):
        self._stack.pop(len(self._stack) - 1)

    def get_formula(self):
        children = list()
        for e in self._stack:
            children.extend(e)
        return And(children)


class PathGenerator:
    pass
