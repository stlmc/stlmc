# builder class for hylaa
import abc
import copy
from functools import reduce

from ..constraints.constraints import *
from ..constraints.operations import *
from ..solver.assignment import Assignment
from ..solver.ode_utils import make_reset_pool
from ..solver.z3 import Z3Solver
from ..util.logger import Logger

'''
base strategy builder class
use info dictionary as information
messenger.
'''


class StrategyBuilder:
    def __init__(self):
        self.info = dict()
        self.arg_names = list()

    def assert_keys(self):
        assert reduce(lambda res, x: res and x in self.arg_names, self.info.keys())

    def prepare(self, info: dict):
        self.info = info

    @abc.abstractmethod
    def perform(self):
        pass


class UnsatCoreBuilder(StrategyBuilder):
    def __init__(self):
        super().__init__()
        self.arg_names = ["alpha", "assignment", "max_bound",
                          "new_abstracted_consts", "c",
                          "optimize", "reduction_flag"]

    def perform(self):
        self.assert_keys()
        alpha = self.info["alpha"]
        assignment = self.info["assignment"]
        max_bound = self.info["max_bound"]
        new_abstracted_consts = self.info["new_abstracted_consts"]
        c = self.info["c"]
        optimize = self.info["optimize"]
        reduction_flag = self.info["reduction_flag"]

        c = self.apply_unsat_core(c, new_abstracted_consts, assignment, is_formula_reduction=reduction_flag)
        max_literal_set_list = list()
        reach_min_bound = 1000000
        is_reach = False

        for i in range(max_bound + 1):
            forall_set, integral_set, init_set, tau_set, reset_set, guard_set = unit_split(c, i)
            new_set = set()
            for cc in forall_set:
                if not isinstance(cc, Not):
                    new_set.add(cc)
            for cc in integral_set:
                if not isinstance(cc, Not):
                    new_set.add(cc)
            for cc in init_set:
                new_set.add(reduce_not(cc))
            for cc in tau_set:
                new_set.add(cc)
            for cc in reset_set:
                if not isinstance(cc, Not):
                    new_set.add(cc)
            for cc in guard_set:
                if isinstance(cc, Bool):
                    if "reach_goal_" in cc.id:
                        is_reach = True
                        cur_min = int(cc.id[cc.id.rfind("_") + 1:])
                        if reach_min_bound > cur_min:
                            reach_min_bound = cur_min
                new_set.add(reduce_not(cc))
            s_diff = set()
            if not optimize:
                for se in new_set:
                    if isinstance(se, Bool):
                        if "newTau" in se.id:
                            s_diff.add(se)
            if is_reach:
                for se in new_set:
                    if get_max_bound(se) > reach_min_bound:
                        s_diff.add(se)
            new_set = new_set.difference(s_diff)

            max_literal_set_list.append(new_set)

        return max_literal_set_list

    def apply_unsat_core(self, c_max, psi, assignment: Assignment, is_formula_reduction=False):
        c_sat = set()
        c_unsat = set()

        assign_dict = assignment.get_assignments()

        for c in c_max:
            if isinstance(c, Bool) and not (c in assign_dict):
                c_unsat.add(Not(c))
            elif assignment.eval(c):
                c_sat.add(c)
            else:
                c_unsat.add(Not(c))
        new_c = c_sat.union(c_unsat)
        index = 0
        assertion_and_trace = list()
        for c in new_c:
            assertion_and_trace.append((c, Bool("trace_var_" + str(index))))
            index += 1

        solver = Z3Solver()
        if is_formula_reduction:
            model_unsat_list = psi.children.copy()
            del model_unsat_list[1]
            goal_unsat_list = psi.children.copy()
            del goal_unsat_list[0]
            del_model_rel = goal_unsat_list[0].children[1:].copy()
            del goal_unsat_list[0]
            goal_unsat_list.extend(del_model_rel)
            model_unsat_core_set = solver.unsat_core(And(model_unsat_list), assertion_and_trace)
            goal_unsat_core_set = solver.unsat_core(And(goal_unsat_list), assertion_and_trace)
            total = model_unsat_core_set.union(goal_unsat_core_set)
            return total
        return solver.unsat_core(psi, assertion_and_trace)


# Common max literal interface for naive and delta debugging
class CommonMaxLiteral:
    @abc.abstractmethod
    def solve_strategy_aux(self, alpha_delta, bound, z3_boolean_consts, boolean_const_model, boolean_sub_dict):
        pass

    def get_max_literal(self, alpha, assignment, max_bound, c, optimize, z3_boolean_consts, boolean_sub_dict):
        c_sat = set()
        c_unsat = set()
        total = dict()

        assign_const = list()

        for b in boolean_sub_dict:
            if not isinstance(b, Bool):
                if assignment.eval(b):
                    assign_const.append(boolean_sub_dict[b])
                else:
                    if not "newTau" in boolean_sub_dict[b].id:
                        assign_const.append(Not(boolean_sub_dict[b]))

        boolean_variables = list()
        for a in alpha:
            if isinstance(a, Bool):
                boolean_variables.append(a.id)

        for c_elem in c:
            vs = get_vars(c_elem)
            flag = True

            for c_vs in vs:
                if c_vs.id in boolean_variables or "newPropDecl" in c_vs.id or "chi" in c_vs.id or "invAtomicID" in c_vs.id or "newIntegral" in c_vs.id:
                    flag = False
                    if c_vs not in alpha:
                        pass
                    elif str(alpha[c_vs]) == "True":
                        total[c_vs] = alpha[c_vs]
                        c_sat.add(c_vs)
                    elif str(alpha[c_vs]) == "False":
                        total[c_vs] = alpha[c_vs]
                        c_unsat.add(Not(c_vs))
                    else:
                        flag = True
                    break

            if flag:
                if assignment.eval(c_elem):
                    total[c_elem] = BoolVal("True")
                    c_sat.add(c_elem)
                else:
                    total[c_elem] = BoolVal("False")
                    c_unsat.add(Not(c_elem))

        alpha_delta = total

        max_literal_set_list = list()
        total_set = c_sat.union(c_unsat)

        for i in range(max_bound + 1):
            max_literal_set, alpha_delta = self.get_max_literal_aux(i, c_sat.union(c_unsat), alpha_delta, optimize,
                                                                    z3_boolean_consts, boolean_sub_dict, assign_const)

            max_literal_set_list.append(max_literal_set)
        return max_literal_set_list, alpha_delta

    def get_max_literal_aux(self, i, c_sat, alpha_delta: dict, optimize, z3_boolean_consts, boolean_sub_dict,
                            assign_const):
        forall_set, integral_set, init_set, tau_set, reset_set, guard_set = unit_split(c_sat, i)
        reset_pool = make_reset_pool(reset_set)

        diff = set()

        for c in alpha_delta:
            if c in integral_set:
                for v in get_vars(c):
                    diff.add(v)
            elif c in reset_set:
                diff.add(c)
        for c in diff:
            del alpha_delta[c]

        for integral in integral_set:
            append_boolean_const = list()
            for v in get_vars(integral):
                alpha_delta[v] = BoolVal("True")
            for reset in reset_pool:
                for r in reset:
                    alpha_delta[r] = BoolVal("True")
                for b in boolean_sub_dict:
                    if isinstance(b, Bool):
                        if b not in alpha_delta:
                            pass
                        elif str(alpha_delta[b]) == "True":
                            append_boolean_const.append(b)
                        else:
                            append_boolean_const.append(Not(b))

                last_boolean_const = assign_const + append_boolean_const

                max_literal_set, alpha_delta = self.solve_strategy_aux(alpha_delta, i, z3_boolean_consts,
                                                                       last_boolean_const, boolean_sub_dict)

                if max_literal_set is not None and alpha_delta is not None:
                    if not optimize:
                        s_diff = set()
                        for se in max_literal_set:
                            if isinstance(se, Bool):
                                if "newTau" in se.id:
                                    s_diff.add(se)
                        max_literal_set = max_literal_set.difference(s_diff)

                    return max_literal_set, alpha_delta


class NaiveBuilder(StrategyBuilder, CommonMaxLiteral):
    def __init__(self):
        super().__init__()
        self.arg_names = ["alpha", "assignment", "max_bound", "c",
                          "optimize", "z3_boolean_consts", "boolean_sub_dict"]

    def perform(self):
        self.assert_keys()
        alpha = self.info["alpha"]
        assignment = self.info["assignment"]
        max_bound = self.info["max_bound"]
        c = self.info["c"]
        optimize = self.info["optimize"]
        z3_boolean_consts = self.info["z3_boolean_consts"]
        boolean_sub_dict = self.info["boolean_sub_dict"]

        return self.get_max_literal(alpha, assignment, max_bound, c, optimize, z3_boolean_consts, boolean_sub_dict)

    def solve_strategy_aux(self, alpha_delta, bound, z3_boolean_consts, boolean_const_model, boolean_sub_dict):
        # solve_start = timer()
        solver = Z3Solver()
        dummy_logger = Logger()
        solver.append_logger(dummy_logger)

        solver.add(And(boolean_const_model))
        result = solver.solve()

        if not result[0]:
            assignment = solver.make_assignment()

            simplified_result = assignment.z3eval(z3_boolean_consts)

            s_abs_set = set()
            if str(simplified_result) == "True":
                for c in alpha_delta:
                    b_forall, b_integral, b_zero, b_tau, b_reset, b_guard = unit_split({c}, bound)
                    if (len(b_forall) == 1 or len(b_integral) == 1 or len(b_zero) == 1 or
                            len(b_tau) == 1 or len(b_reset) == 1 or len(b_guard) == 1):
                        if str(alpha_delta[c]) == 'True' and not isinstance(c, Neq):
                            s_abs_set.add(c)

                return s_abs_set, alpha_delta

        return None, alpha_delta


class DeltaDebugBuilder(StrategyBuilder, CommonMaxLiteral):
    def __init__(self):
        super().__init__()
        self.arg_names = ["alpha", "assignment", "max_bound", "c",
                          "optimize", "z3_boolean_consts", "boolean_sub_dict"]

    def perform(self):
        self.assert_keys()
        alpha = self.info["alpha"]
        assignment = self.info["assignment"]
        max_bound = self.info["max_bound"]
        c = self.info["c"]
        optimize = self.info["optimize"]
        z3_boolean_consts = self.info["z3_boolean_consts"]
        boolean_sub_dict = self.info["boolean_sub_dict"]
        return self.get_max_literal(alpha, assignment, max_bound, c, optimize, z3_boolean_consts, boolean_sub_dict)

    def solve_strategy_aux(self, alpha_delta, bound, z3_boolean_consts, boolean_const_model, boolean_sub_dict):
        solver = Z3Solver()
        solver.set_logic('lra')
        solver.add(And(boolean_const_model))
        if not solver.solve()[0]:
            assignment = solver.make_assignment()

            simplified_result = assignment.z3eval(z3_boolean_consts)

            s_abs_set = set()

            if str(simplified_result) == "True":
                for c in alpha_delta:
                    b_forall, b_integral, b_zero, b_tau, b_reset, b_guard = unit_split({c}, bound)
                    if (len(b_forall) == 1 or len(b_integral) == 1 or len(b_zero) == 1 or
                            len(b_tau) == 1 or len(b_reset) == 1 or len(b_guard) == 1):
                        if str(alpha_delta[c]) == 'True' and not isinstance(c, Neq):
                            s_abs_set.add(c)

                return self.delta_debugging(s_abs_set, z3_boolean_consts, boolean_sub_dict), alpha_delta

        return None, alpha_delta

    def delta_debugging_aux(self, c_max: set, z3_boolean_consts, boolean_sub_dict):
        if len(c_max) == 0:
            return set()
        alpha = dict()
        boolean_const_model = list()
        for c in c_max:
            alpha[c] = BoolVal("True")
            boolean_const_model.append(boolean_sub_dict[c])

        for c in c_max:
            new_alpha = alpha.copy()
            revise_boolean_const = copy.deepcopy(boolean_const_model)
            new_alpha[c] = BoolVal("False")
            revise_boolean_const.remove(boolean_sub_dict[c])
            revise_boolean_const.append(Not(boolean_sub_dict[c]))
            solver = Z3Solver()
            solver.set_logic('lra')
            solver.add(And(revise_boolean_const))
            if not solver.solve()[0]:
                assignment = solver.make_assignment()

                simplified_result = assignment.z3eval(z3_boolean_consts)

                if str(simplified_result) == "True":
                    return self.delta_debugging_aux(c_max.difference({c}), z3_boolean_consts, boolean_sub_dict)

        return c_max

    def delta_debugging(self, c_max, z3_boolean_consts, boolean_sub_dict):
        return self.delta_debugging_aux(c_max, z3_boolean_consts, boolean_sub_dict)


def unit_split(given_set: set, i: int):
    forall_set = set()
    integral_set = set()
    tau_set = set()
    guard_set = set()
    reset_set = set()
    init_set = set()

    s_diff = set()

    for c in given_set:
        if isinstance(c, Not):
            s_diff.add(c)

    given_set = given_set.difference(s_diff)

    for c in given_set:
        var_set = get_vars(c)
        if len(var_set) == 1:
            for var in var_set:
                start_index = int(var.id.find("_"))
                if var.id[start_index:] == "_0_0" and "newTau" not in var.id and "newIntegral" not in var.id and "invAtomicID" not in var.id:
                    init_set.add(c)
                    s_diff.add(c)
                    break

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        var_set = get_vars(c)
        for var in var_set:
            start_index = int(var.id.find("_"))
            s_index = int(var.id.find("_"))
            e_index = int(var.id.rfind("_"))
            bound_index = int(var.id.rfind("_"))
            if not (s_index == -1):
                if (s_index == e_index and "tau" not in var.id) or ("newPropDecl" in var.id):
                    bound = int(var.id[bound_index + 1:]) // 2
                    if i == bound:
                        forall_set.add(c)
                        s_diff.add(c)
                        break
                if "invAtomicID" in var.id:
                    bound = int(var.id[bound_index + 1:])
                    if i == bound:
                        forall_set.add(c)
                        s_diff.add(c)
                        break
            if var.id[:start_index] == "newIntegral":
                bound = int(var.id[bound_index + 1:])
                if i == bound:
                    integral_set.add(c)
                    s_diff.add(c)
                    break

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        var_set = get_vars(c)
        max_bound = -1
        for var in var_set:
            start_index = int(var.id.find("_"))
            if var.id[:start_index] == "tau":
                bound = int(var.id[start_index + 1:])
                if max_bound < bound:
                    max_bound = bound
        if (max_bound == 0 and i == 0) or (max_bound != -1 and max_bound == i + 1):
            tau_set.add(c)
            s_diff.add(c)
        elif isinstance(c, Bool):
            if "newTau" in c.id and int(c.id[-1]) == i:
                tau_set.add(c)
                s_diff.add(c)

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        if isinstance(c, Eq):
            if isinstance(c.left, Variable):
                start_index = int(c.left.id.find("_"))
                end_index = int(c.left.id.rfind("_"))
                if start_index < end_index:
                    bound = int(c.left.id[start_index + 1:end_index])
                    if c.left.id[end_index + 1:] == "0" and bound == i + 1:
                        reset_set.add(c)
                        s_diff.add(c)

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        var_set = get_vars(c)
        flag = True
        for var in var_set:
            start_index = int(var.id.find("_"))
            s_index = int(var.id.find("_"))
            e_index = int(var.id.rfind("_"))
            end_index = int(var.id.rfind("_"))
            if not (s_index == e_index or "newIntegral" in var.id or "invAtomicID" in var.id
                    or "newPropDecl" in var.id or "newTau" in var.id or "reach_goal" in var.id or "chi" in var.id or "opt_var" in var.id):
                bound = int(var.id[start_index + 1:end_index])
                last_str = var.id[-1]
                if not ((bound == i and last_str == "t") or (bound == i + 1 and last_str == "0")):
                    flag = False
                '''
                if isinstance(c.left, Real):
                    if c.left.id[e_index + 1:] == "0":
                        flag = False
                        break
                '''
            else:
                flag = False
        if flag:
            guard_set.add(c)
            s_diff.add(c)
        if isinstance(c, Bool):
            if "reach_goal_" in c.id:
                guard_set.add(c)

    return forall_set, integral_set, init_set, tau_set, reset_set, guard_set