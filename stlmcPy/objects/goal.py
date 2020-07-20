import stlmcPy.constraints.partition as PART
import stlmcPy.constraints.separation as SEP
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_vars, substitution, make_dict, relaxing, reduce_not
import stlmcPy.constraints.encoding as ENC
import abc


class Goal:
    @abc.abstractmethod
    def make_consts(self, bound, time_bound, delta, model, proposition_dict):
        pass

    @abc.abstractmethod
    def get_formula(self):
        pass


class PropHelper:
    def __init__(self, goal: Goal, model, proposition_dict):
        self.goal = goal
        self.model = model
        self.proposition_dict = proposition_dict

    def make_integrals(self, bound):
        mode_number = 1
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
            integral = Integral(mode_number, end_vector, start_vector, dynamics)
            integrals.append(integral)
            mode_number += 1
        return integrals

    def make_consts(self, bound, delta):
        goal_vars = get_vars(self.goal.get_formula())
        integrals = self.make_integrals(bound)
        substitute_dict = make_dict(bound, self.model.mode_var_dict, self.model.range_dict, self.model.const_dict, "_0")

        new_substitute_dict = substitute_dict.copy()
        for prop_var in self.proposition_dict:
            new_substitute_dict[prop_var] = Bool(prop_var.id + "_" + str(bound))

        result_children = list()
        for goal_var in goal_vars:
            if goal_var in self.proposition_dict:
                index = 0
                goal_sub_children = list()
                for mode_module in self.model.modules:
                    integral = integrals[index]
                    const = self.proposition_dict[goal_var]
                    bound_applied_goal_var = substitution(goal_var, new_substitute_dict)
                    bound_applied_const = substitution(const, new_substitute_dict)
                    relaxed_bound_const = relaxing(bound_applied_const, RealVal(str(delta)))
                    goal_sub_children.append(Or([Eq(bound_applied_goal_var, Forall(integral.current_mode_number,
                                                                                   Real(
                                                                                       'tau_' + str(bound + 1)),
                                                                                   Real('tau_' + str(bound)),
                                                                                   relaxed_bound_const,
                                                                                   integral)),
                                                 Eq(Not(bound_applied_goal_var), Forall(integral.current_mode_number,
                                                                                        Real(
                                                                                            'tau_' + str(bound + 1)),
                                                                                        Real('tau_' + str(bound)),
                                                                                        reduce_not(Not(relaxed_bound_const)),
                                                                                        integral))]))

                    index += 1
                result_children.append(Or(goal_sub_children))
        return And(result_children)


class BaseStlGoal(Goal):
    # get core.formula. of some type...
    def __init__(self, formula: Formula):
        self.formula = formula

    @abc.abstractmethod
    def make_stl_consts(self, bound):
        pass

    def make_time_consts(self, bound, time_bound):
        time_const_children = list()
        for k in range(bound + 2):
            time_const_children.append(Leq(RealVal('0'), Real('tau_' + str(k))))
            time_const_children.append(Leq(Real('tau_' + str(k)), RealVal(str(time_bound))))
            if k < bound + 1:
                time_const_children.append(Lt(Real('tau_' + str(k)), Real('tau_' + str(k + 1))))
        return And(time_const_children)

    def get_formula(self):
        return self.formula

    def make_consts(self, bound, time_bound, delta, model, proposition_dict):
        # generate mapping constraint between model and goal
        propHelper = PropHelper(self, model, proposition_dict)

        result_const = list()
        for k in range(bound + 1):
            mapping_consts = propHelper.make_consts(k, delta)
            result_const.append(mapping_consts)

        stl_consts = self.make_stl_consts(bound)
        time_consts = self.make_time_consts(bound, time_bound)

        result_const.append(stl_consts)
        result_const.append(time_consts)
        return And(result_const)


class OldStlGoal(BaseStlGoal):
    def make_stl_consts(self, bound):
        pass


class NewStlGoal(BaseStlGoal):
    def make_stl_consts(self, bound):
        baseP = PART.baseCase(bound)
        negFormula = Not(self.formula)

        (partition, sepMap) = PART.guessPartition(negFormula, baseP)
        fs = SEP.fullSeparation(negFormula, sepMap)

        originalFS = dict()
        for (m, n) in fs[1].keys():
            originalFS[m] = fs[1][(m, n)]

            # FOL translation
        baseV = ENC.baseEncoding(partition, baseP)
        (formulaConst, subFormulaMap) = ENC.valuation(fs[0], originalFS, ENC.Interval(True, 0.0, True, 0.0), baseV)

        # partition constraints
        partition_const_children = PART.genPartition(baseP, fs[1], subFormulaMap)
        return And(partition_const_children)


class ReachGoal(Goal):
    # get core.formula. of some type...
    def __init__(self, formula: Formula):
        self.formula = formula

    def get_formula(self):
        return self.formula

    def make_consts(self, bound, time_bound, delta, model, proposition_dict):
        # return to original const
        decoded_consts = substitution(self.formula, proposition_dict)

        # make goal speciific dictionary and substitute it
        goal_dict = make_dict(bound, model.mode_var_dict, model.range_dict, model.const_dict, "_t")
        goal_consts = substitution(decoded_consts, goal_dict)
        return goal_consts


class GoalFactory:
    def __init__(self, raw_goal: Formula):
        self.raw_goal = raw_goal

    def generate_goal(self):
        if isinstance(self.raw_goal, Reach):
            return ReachGoal(self.raw_goal.formula)
        else:
            return NewStlGoal(self.raw_goal)
        pass
