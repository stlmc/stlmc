import abc
from abc import ABC
from typing import Dict, Set, Tuple

from ..constraints.aux.operations import reduce_not
from ..constraints.constraints import *
from ..encoding.base_encoder import Encoder


class Goal(Encoder):
    def __init__(self, formula: Formula):
        self.formula = formula

    @abc.abstractmethod
    def encode(self):
        pass

    # TODO: rename this to get_raw_goal
    def get_formula(self):
        return self.formula


# for reach optimization
def optimize(formula: Formula) -> Formula:
    def _check_if_suitable(_formula: Formula):
        if _formula is None or not isinstance(_formula, GloballyFormula):
            return False
        count = 0
        waiting_queue = set()
        waiting_queue.add((count, _formula))
        while len(waiting_queue) > 0:
            count = count + 1
            _, t = waiting_queue.pop()
            if isinstance(t, Leaf):
                pass
            elif isinstance(t, NonLeaf):
                if (isinstance(t, UnaryTemporalFormula) or isinstance(t, BinaryTemporalFormula)) and count > 1:
                    return False
                for child in t.children:
                    waiting_queue.add((count, child))
            else:
                continue
        return True

    def _transform(_formula: GloballyFormula) -> Formula:
        # local : [0, inf] => ..
        # local : [a , b] => tau \in [a, b]
        _local = _formula.local_time
        assert isinstance(_local, Interval)
        _tau = Real("tau")
        _zero = RealVal("0.0")
        _inf = RealVal("inf")
        if _local.left.value == _zero.value and _local.right.value == _inf.value:
            return Not(_formula.child)

        _op_dict = {True: Leq, False: Lt}
        _left_const = _op_dict[_local.left_end](_local.left, _tau)
        _right_const = _op_dict[_local.right_end](_tau, _local.right)
        return And([_left_const, _right_const, Not(_formula.child)])

    formula = reduce_not(formula)
    if _check_if_suitable(formula):
        assert isinstance(formula, GloballyFormula)
        return _transform(formula)
    return formula


def reach_goal(goal: Goal) -> Goal:
    return ReachGoal(goal.get_formula(), goal.time_encoding_function)
