import stlmcPy.constraints.enhanced_partition as ENHANCED_PART
import stlmcPy.constraints.enhanced_separation as ENHANCED_SEP
import stlmcPy.constraints.separation as SEP
import stlmcPy.constraints.partition as PART
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_vars, substitution, make_dict, relaxing, reduce_not, make_new_dynamics, \
    lower_encoding, bound_tau_max
import stlmcPy.constraints.encoding as ENC
import abc
from timeit import default_timer as timer


class Goal:

    def make_time_consts(self, bound, time_bound):
        time_const_children = list()
        for k in range(1, bound + 1):
            if k == 1:
                chi = Geq(Real('tau_' + str(k)), RealVal('0'))
                time_const_children.append(chi)
            if k < bound :
                time_const_children.append(Leq(Real('tau_' + str(k)), Real('tau_' + str(k + 1))))
            elif k == bound:
                chi = Lt(Real('tau_' + str(k)), RealVal(str(time_bound)))
                time_const_children.append(chi)

        time_const_children.append(Eq(Real('tau_' + str(bound + 1)), RealVal(str(time_bound))))

        return time_const_children

    @abc.abstractmethod
    def make_consts(self, bound, time_bound, delta, model, proposition_dict):
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
            all_vars_list = sorted(all_vars_list, key= lambda x: x.id)

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

            #for goal_var in goal_vars:
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

                    #relaxed_bound_const = relaxing(bound_applied_const, RealVal(str(delta)))

                    #not_relaxed_bound_const = relaxing(reduce_not(Not(bound_applied_const)), RealVal(str(delta)))

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
    def __init__(self, formula: Formula):
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

        '''
        for k in range(bound + 1):
            mapping_consts = propHelper.make_consts(k, delta)
            prop_const.extend(mapping_consts)
        '''

        result_const.append(And(prop_const))

        stl_consts_list = self.make_stl_consts(bound, time_bound)

        time_consts_list = self.make_time_consts(bound, time_bound)

        result_const.extend(time_consts_list)
        result_const.extend(stl_consts_list)
        boolean_abstract = dict()
        boolean_abstract.update(self.boolean_abstract)
        boolean_abstract.update(propHelper.boolean_abstract)

        return And(result_const), boolean_abstract


class OldStlGoal(BaseStlGoal):
    def make_stl_consts(self, bound, time_bound):
        baseP = PART.baseCase(bound)
        negFormula = reduce_not(Not(self.formula))
        negFormula = bound_tau_max(negFormula, time_bound)

        # partition constraint
        (partition, sepMap, partitionConsts) = PART.guessPartition(negFormula, baseP)

        # full separation
        fs = SEP.fullSeparation(negFormula, sepMap)


        # set enc flags
        ENC.ENC_TYPES = "old"
        # FOL translation

        baseV = ENC.baseEncoding(partition, baseP, time_bound)

        formulaConst = ENC.valuation(fs[0], fs[1], ENC.Interval(True, 0.0, True, 0.0), baseV)[0]

        total_children = list()
        total_children.extend(formulaConst)
        total_children.extend(partitionConsts)

        return total_children


class NewStlGoal(BaseStlGoal):
    def make_stl_consts(self, bound, time_bound):
        baseP = ENHANCED_PART.baseCase(bound)
        negFormula = reduce_not(Not(self.formula))

        (partition, sepMap) = ENHANCED_PART.guessPartition(negFormula, baseP)

        sub_list = list(partition.keys())

        consts = list()

        (var_point, var_interval) = ENHANCED_SEP.make_time_list(bound)
        id_match_dict = dict()
        for s in range(len(sub_list)):
            id_match_dict[sub_list[s]] = Bool("chi_" + str(s))

        for sub in id_match_dict:
            if isinstance(sub, Bool):
                sub_const = lower_encoding(id_match_dict[sub].id, bound, 2)

        # for s in range(len(sub_list)):
        #     consts.extend(ENHANCED_SEP.fullSeparation(s, sub_list[s], var_point, var_interval, id_match_dict))
        #     constraints, self.boolean_abstract = ENHANCED_PART.genPartition(sub_list[s], sub_list, bound)
        #     consts.extend(constraints)
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


class ReachGoal(Goal):
    # get core.formula. of some type...
    def __init__(self, formula: Formula):
        self.formula = formula

    def get_formula(self):
        return self.formula

    def make_consts(self, bound, time_bound, delta, model, proposition_dict):
        # if len(proposition_dict) == 0:
        #    return BoolVal("True"), dict()

        result = list()
        # return to original const
        decoded_consts = substitution(self.formula, proposition_dict)
        sub_result = list()

        # make goal speciific dictionary and substitute it
        for cur_bound in range(0, bound + 1):
            goal_dict = make_dict(cur_bound, model.mode_var_dict, model.range_dict, model.const_dict, "_t")
            goal_consts = substitution(decoded_consts, goal_dict)
            # cur_bool = Bool("reach_goal_" + str(cur_bound))
            # sub_result.append(And([cur_bool, goal_consts]))
            sub_result.append(goal_consts)
        # get time const
        result.append(Or(sub_result))
        result.extend(self.make_time_consts(bound, time_bound))

        return And(result), dict()


class GoalFactory:
    def __init__(self, raw_goal: Formula):
        self.raw_goal = raw_goal

    @abc.abstractmethod
    def generate_goal(self):
        if isinstance(self.raw_goal, Reach):
            return ReachGoal(self.raw_goal.formula)
        else:
            return NewStlGoal(self.raw_goal)
        pass


class OldGoalFactory(GoalFactory):
    def __init__(self, raw_goal: Formula):
        super().__init__(raw_goal)

    def generate_goal(self):
        if isinstance(self.raw_goal, Reach):
            return ReachGoal(self.raw_goal.formula)
        else:
            return OldStlGoal(self.raw_goal)
        pass
