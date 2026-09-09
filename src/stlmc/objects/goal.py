import abc

from ..constraints.constraints import (
    And, BinaryTemporalFormula, Bool, BoolVal, Formula, GloballyFormula,
    Interval, Leaf, Leq, Lt, NonLeaf, Not, Or, Real, RealVal,
    UnaryTemporalFormula,
)
from ..constraints.logical_normalization import reduce_not
from ..constraints.model_transform import make_dict
from ..constraints.robustness_transform import relaxing
from ..constraints.substitution import substitution
from ..encoding.time import make_zeno_time_const, make_non_zeno_time_const
from ..exceptions import NotSupportedError


class Goal(abc.ABC):
    def __init__(self, time_enc_func):
        self.time_encoding_function = time_enc_func
        self.partition_size = 0

    @abc.abstractmethod
    def get_formula(self):
        pass

    @abc.abstractmethod
    def clear(self):
        pass


class StlGoal(Goal):
    """Formula container encoded by the shared bounded-STL layer."""

    def __init__(self, formula: Formula, time_enc_func=None):
        super().__init__(time_enc_func or make_zeno_time_const)
        self.formula = formula

    def get_formula(self):
        return self.formula

    def clear(self):
        pass


class ReachGoal(Goal):
    def clear(self):
        pass

    # get core.formula. of some type...
    def __init__(self, formula: Formula, time_enc_func=None):
        if time_enc_func is None:
            super().__init__(make_zeno_time_const)
        else:
            super().__init__(time_enc_func)
        self.formula = formula
        assert isinstance(formula, Formula)
        # assert is_proposition(self.formula)

    def get_formula(self):
        return self.formula

    def make_consts(self, bound, time_bound, delta, model, proposition_dict):
        def _update_negation_prop(_prop_dict: dict) -> dict:
            _new_dict = dict()
            for _p in _prop_dict:
                _new_dict[_p] = _prop_dict[_p]
                if isinstance(_p, Bool):
                    if "newPropDecl_" in _p.id:
                        _new_dict[Bool("not@{}".format(_p.id))] = reduce_not(Not(_prop_dict[_p]))
            return _new_dict

        updated_proposition_dict = _update_negation_prop(proposition_dict)

        result = list()
        # return to original const
        decoded_consts = substitution(self.formula, updated_proposition_dict)
        decoded_consts = relaxing(decoded_consts, float(delta))
        sub_result = list()

        # make goal specific dictionary and substitute it
        for cur_bound in range(0, bound + 1):
            goal_dict = make_dict(cur_bound, model.mode_var_dict, model.range_dict, model.const_dict, "_t")
            goal_dict[Real("tau")] = Real("tau_{}".format(cur_bound + 1))
            goal_consts = substitution(decoded_consts, goal_dict)
            sub_result.append(goal_consts)
        # get time const
        result.append(Or(sub_result))
        result.extend(self.time_encoding_function(bound, time_bound))

        return And(result), dict()

    def k_step_consts(self, k, time_bound, delta, model, proposition_dict, is_final=False):
        # k: bound, not depth
        if is_final:
            return BoolVal("True")

        goal_start_dict = make_dict(k, model.mode_var_dict, model.range_dict, model.const_dict, "_0")
        goal_end_dict = make_dict(k, model.mode_var_dict, model.range_dict, model.const_dict, "_t")

        decoded_consts = substitution(self.formula, proposition_dict)
        decoded_consts = relaxing(decoded_consts, float(delta))

        start_consts = substitution(decoded_consts, goal_start_dict)
        end_consts = substitution(decoded_consts, goal_end_dict)

        return Or([start_consts, end_consts])


def validate_reach_formula(formula: Formula):
    """Reject temporal reach targets; reachability is defined for states."""
    waiting = [formula]
    while waiting:
        current = waiting.pop()
        if isinstance(current, (UnaryTemporalFormula, BinaryTemporalFormula)):
            raise NotSupportedError(
                "reachability requires a state formula without temporal operators: {}"
                .format(formula)
            )
        if isinstance(current, NonLeaf):
            waiting.extend(current.children)


class GoalFactory:
    def __init__(self, raw_goal: Formula, is_zeno=True):
        self.raw_goal = raw_goal
        self.time_function = None
        if is_zeno:
            self.time_function = make_zeno_time_const
        else:
            self.time_function = make_non_zeno_time_const

    def generate_goal(self, is_reach=False):
        if is_reach:
            return ReachGoal(self.raw_goal, self.time_function)
        return StlGoal(self.raw_goal, self.time_function)


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
