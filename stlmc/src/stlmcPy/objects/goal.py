import abc

from ..constraints import encoding as ENC
from ..constraints import enhanced_partition as ENHANCED_PART
from ..constraints import enhanced_separation as ENHANCED_SEP
from ..constraints import partition as PART
from ..constraints import separation as SEP
from ..constraints.operations import *
from ..encoding.time import make_zeno_time_const, make_non_zeno_time_const


class Goal:
    def __init__(self, time_enc_func):
        self.time_encoding_function = time_enc_func
        self.partition_size = 0

    @abc.abstractmethod
    def make_consts(self, bound, time_bound, delta, model, proposition_dict):
        pass

    @abc.abstractmethod
    def k_step_consts(self, k, time_bound, delta, model, proposition_dict, is_final=False):
        pass

    @abc.abstractmethod
    def get_formula(self):
        pass

    @abc.abstractmethod
    def clear(self):
        pass


class PropHelper:
    def __init__(self, goal: Goal, model, proposition_dict, bound):
        self.goal = goal
        self.model = model
        self.proposition_dict = proposition_dict
        self.boolean_abstract = dict()
        self.bound = bound

    def make_integrals(self, bound):
        mode_number = 0
        integrals = list()
        for mode_module in self.model.modules:
            dynamics = mode_module["flow"]
            start_vector = list()
            end_vector = list()

            index = 0
            for exp in dynamics.exps:
                flow_var_id = dynamics.vars[index].id
                start_vector.append(Real(flow_var_id + "_" + str(bound) + "_0"))
                end_vector.append(Real(flow_var_id + "_" + str(bound) + "_t"))
                index += 1
            integral = Integral(mode_number, end_vector, start_vector, dynamics)
            integrals.append(integral)
            mode_number += 1
        return integrals

    def make_consts(self, delta):
        result_children = list()
        if len(self.proposition_dict) == 0:
            return result_children
        mode_set = set(self.model.mode_var_dict.values())
        for bound in range(0, self.bound + 1):
            # don't do anything when there is nothing to do.
            goal_vars = get_vars(self.goal.get_formula())
            all_vars_list = list(goal_vars)
            all_vars_list = sorted(all_vars_list, key=lambda x: x.id)

            integrals = self.make_integrals(bound)
            substitute_dict = make_dict(bound, self.model.mode_var_dict, self.model.range_dict, self.model.const_dict,
                                        "_0")
            dynamics_list = list()
            sub_integrals_list = list()
            for chi in integrals:
                new_dynamics = make_new_dynamics(chi.dynamics, bound, self.model.mode_var_dict, self.model.range_dict,
                                                 self.model.const_dict)
                sub_integrals_list.append(
                    Integral(chi.current_mode_number, chi.end_vector, chi.start_vector, new_dynamics))

            new_substitute_dict_point = substitute_dict.copy()
            new_substitute_dict_interval = substitute_dict.copy()
            for prop_var in self.proposition_dict:
                new_substitute_dict_point[prop_var] = Bool(prop_var.id + "_" + str(2 * bound))
                new_substitute_dict_interval[prop_var] = Bool(prop_var.id + "_" + str(2 * bound + 1))

            # for goal_var in goal_vars:
            for goal_var in all_vars_list:
                if goal_var in self.proposition_dict:
                    index = 0
                    integral = integrals[index]
                    const = self.proposition_dict[goal_var]

                    # mode condition checking get_vars(const))
                    isMode = False
                    if len(get_vars(const) - mode_set) == 0:
                        isMode = True

                    bound_applied_goal_var = substitution(goal_var, new_substitute_dict_point)
                    bound_applied_goal_interval = substitution(goal_var, new_substitute_dict_interval)

                    bound_applied_const = substitution(const, new_substitute_dict_point)

                    if isinstance(bound_applied_const, Eq):
                        if isinstance(bound_applied_const.left, Bool) or isinstance(bound_applied_const.right, Bool):
                            sub = list()
                            sub.append(Eq(Bool("not@" + bound_applied_goal_var.id),
                                          Neq(bound_applied_const.left, bound_applied_const.right)))
                            sub.append(Eq(Bool(bound_applied_goal_var.id), bound_applied_const))
                            return sub

                    # relaxed_bound_const = relaxing(bound_applied_const, RealVal(str(delta)))

                    # not_relaxed_bound_const = relaxing(reduce_not(Not(bound_applied_const)), RealVal(str(delta)))

                    relaxed_bound_const = bound_applied_const
                    not_relaxed_bound_const = reduce_not(Not(bound_applied_const))

                    not_bound_applied_goal_var = Bool("not@" + bound_applied_goal_var.id)
                    not_bound_applied_goal_interval = Bool("not@" + bound_applied_goal_interval.id)

                    # fair_const_1 = Or([Not(bound_applied_goal_var), Not(not_bound_applied_goal_var)])
                    fair_const_2 = Or([bound_applied_goal_var, not_bound_applied_goal_var])
                    init_const_1 = Eq(bound_applied_goal_var, relaxed_bound_const)
                    init_const_2 = Eq(not_bound_applied_goal_var, not_relaxed_bound_const)
                    init_point_check = And([init_const_1, init_const_2, fair_const_2])
                    pos_forall_list = list()
                    neg_forall_list = list()

                    start_tau = Real('tau_' + str(bound))
                    if str(bound) == "0":
                        start_tau = RealVal("0")

                    if isMode:
                        pos_interval_const = relaxed_bound_const
                        neg_interval_const = not_relaxed_bound_const
                    else:
                        for chi in range(len(sub_integrals_list)):
                            pos_forall_list.append(
                                Forall(chi, Real('tau_' + str(bound + 1)), start_tau, relaxed_bound_const,
                                       sub_integrals_list[chi]))
                            neg_forall_list.append(
                                Forall(chi, Real('tau_' + str(bound + 1)), start_tau, not_relaxed_bound_const,
                                       sub_integrals_list[chi]))
                        pos_interval_const = Or(pos_forall_list)
                        neg_interval_const = Or(neg_forall_list)
                    self.boolean_abstract[bound_applied_goal_interval] = pos_interval_const
                    self.boolean_abstract[not_bound_applied_goal_interval] = neg_interval_const

                    result_children.append(Or([bound_applied_goal_interval, not_bound_applied_goal_interval]))

                    result_children.append(init_point_check)

        return result_children


class BaseStlGoal(Goal):
    # get core.formula. of some type...
    def __init__(self, formula: Formula, time_enc_func):
        super().__init__(time_enc_func)
        self.formula = formula
        self.boolean_abstract = dict()

    def clear(self):
        self.boolean_abstract = dict()

    @abc.abstractmethod
    def make_stl_consts(self, bound, time_bound):
        pass

    def get_formula(self):
        return self.formula

    def make_consts(self, bound, time_bound, delta, model, proposition_dict):
        # generate mapping constraint between model and goal
        propHelper = PropHelper(self, model, proposition_dict, bound)

        result_const = list()
        prop_const = propHelper.make_consts(delta)

        result_const.append(And(prop_const))

        stl_consts_list = self.make_stl_consts(bound, time_bound)

        time_consts_list = self.time_encoding_function(bound, time_bound)

        result_const.extend(time_consts_list)
        result_const.extend(stl_consts_list)
        boolean_abstract = dict()
        boolean_abstract.update(self.boolean_abstract)
        boolean_abstract.update(propHelper.boolean_abstract)

        return And(result_const), boolean_abstract

    def k_step_consts(self, k, time_bound, delta, model, proposition_dict, is_final=False):
        pass


class OldStlGoal(BaseStlGoal):
    def make_stl_consts(self, bound, time_bound):
        baseP = PART.baseCase(bound)
        negFormula = reduce_not(Not(self.formula))
        negFormula = bound_tau_max(negFormula, time_bound)

        # partition constraint
        (partition, sepMap, partitionConsts) = PART.guessPartition(negFormula, baseP)
        empty = set()
        for pt in partition.keys():
            empty = empty.union(partition[pt])

        self.partition_size = len(empty)

        # full separation
        fs = SEP.fullSeparation(negFormula, sepMap)

        # set enc flags
        ENC.ENC_TYPES = "old"
        # FOL translation

        baseV = ENC.baseEncoding(partition, baseP, time_bound)

        formulaConst = ENC.valuation(fs[0], fs[1], Interval(True, RealVal("0.0"), True, RealVal("0.0")), baseV)[0]

        total_children = list()
        total_children.extend(formulaConst)
        total_children.extend(partitionConsts)

        return total_children

    def k_step_consts(self, k, time_bound, delta, model, proposition_dict, is_final=False):
        pass


class NewStlGoal(BaseStlGoal):
    def make_stl_consts(self, bound, time_bound):
        baseP = ENHANCED_PART.baseCase(bound)
        negFormula = reduce_not(Not(self.formula))

        (partition, sepMap) = ENHANCED_PART.guessPartition(negFormula, baseP)

        empty = set()
        for pt in partition.keys():
            empty = empty.union(partition[pt])

        self.partition_size = len(empty)

        sub_list = list(partition.keys())

        consts = list()

        (var_point, var_interval) = ENHANCED_SEP.make_time_list(bound)
        id_match_dict = dict()
        for s in range(len(sub_list)):
            id_match_dict[sub_list[s]] = Bool("chi_" + str(s))

        for sub in id_match_dict:
            if isinstance(sub, Bool):
                sub_const = lower_encoding(id_match_dict[sub].id, bound, 2)

        for s in range(len(sub_list)):
            constraints, ba = ENHANCED_SEP.fullSeparation(s, sub_list[s], var_point, var_interval, id_match_dict)
            consts.extend(constraints)
            self.boolean_abstract.update(ba)
            constraints, ba = ENHANCED_PART.genPartition(sub_list[s], sub_list, bound)
            consts.extend(constraints)
            self.boolean_abstract.update(ba)

        str_list = [str(c) for c in sub_list]
        form_index = str_list.index(str(negFormula))

        consts.append(Bool("chi_" + str(form_index) + "_1"))

        return consts

    def k_step_consts(self, k, time_bound, delta, model, proposition_dict, is_final=False):
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

        start_consts = substitution(decoded_consts, goal_start_dict)
        end_consts = substitution(decoded_consts, goal_end_dict)

        return Or([start_consts, end_consts])


class GoalFactory:
    def __init__(self, raw_goal: Formula, is_zeno=True):
        self.raw_goal = raw_goal
        self.time_function = None
        if is_zeno:
            self.time_function = make_zeno_time_const
        else:
            self.time_function = make_non_zeno_time_const

    @abc.abstractmethod
    def generate_goal(self, is_reach=False):
        if is_reach:
            return ReachGoal(self.raw_goal, self.time_function)
        else:
            return NewStlGoal(self.raw_goal, self.time_function)


class OldGoalFactory(GoalFactory):
    def __init__(self, raw_goal: Formula, is_zeno=True):
        super().__init__(raw_goal)
        self.time_function = None
        if is_zeno:
            self.time_function = make_zeno_time_const
        else:
            self.time_function = make_non_zeno_time_const

    def generate_goal(self, is_reach=False):
        if is_reach:
            return ReachGoal(self.raw_goal, self.time_function)
        else:
            return OldStlGoal(self.raw_goal, self.time_function)


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
