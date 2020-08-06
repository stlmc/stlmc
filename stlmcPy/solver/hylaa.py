import abc
from abc import ABC
from functools import singledispatch
from itertools import product
from timeit import default_timer as timer

from sympy import symbols, simplify, StrictGreaterThan, GreaterThan, LessThan, StrictLessThan, Symbol, Float, Equality, \
    Unequality
from sympy.core import relational

from hylaa import symbolic, lputil
from hylaa.core import Core
from hylaa.hybrid_automaton import HybridAutomaton
from hylaa.settings import HylaaSettings
from hylaa.stateset import StateSet
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_boolean_abstraction, inverse_dict, \
    forall_integral_substitution, substitution, reduce_not, get_vars, infix
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.abstract_solver import BaseSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.z3 import Z3Solver


class HylaaStrategy:

    @abc.abstractmethod
    def solve_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c):
        pass

    def get_max_literal(self, alpha, assignment, max_bound, new_abstracted_consts, c):
        c_sat = set()
        c_unsat = set()
        total = dict()

        for c_elem in c:
            vs = get_vars(c_elem)
            flag = True

            for c_vs in vs:
                if "newPropDecl" in c_vs.id or "chi" in c_vs.id or "newIntegral" in c_vs.id or (
                        c_vs.id.count('_') == 1 and 'tau' not in c_vs.id):
                    flag = False
                    if c_vs not in alpha:
                        total[c_vs] = BoolVal("True")
                    elif str(alpha[c_vs]) == "True":
                        total[c_vs] = alpha[c_vs]
                        c_sat.add(c_vs)
                    elif str(alpha[c_vs]) == "False":
                        total[c_vs] = alpha[c_vs]
                        c_unsat.add(Not(c_vs))
                    else:
                        flag = True
                        # raise NotSupportedError("Forall variable assignments problem")
                    break

            if flag:
                if assignment.eval(c_elem):
                    total[c_elem] = BoolVal("True")

                    c_sat.add(c_elem)
                else:
                    total[reduce_not(Not(c_elem))] = BoolVal("True")
                    c_unsat.add(Not(c_elem))

        alpha_delta = total
        max_literal_set_list = list()

        for i in range(max_bound + 1):
            max_literal_set, alpha_delta = self.get_max_literal_aux(new_abstracted_consts, i, c_sat.union(c_unsat),
                                                                    alpha_delta)

            max_literal_set_list.append(max_literal_set)
        return max_literal_set_list, alpha_delta

    def get_max_literal_aux(self, psi_abs, i, c_sat, alpha_delta: dict):
        forall_set, integral_set, init_set, tau_set, reset_set, guard_set = unit_split(c_sat, i)
        reset_pool = make_reset_pool(reset_set)

        for c in alpha_delta:
            if c in integral_set:
                for v in get_vars(c):
                    alpha_delta[v] = BoolVal("False")
            elif c in reset_set:
                alpha_delta[c] = BoolVal("False")

        for integral in integral_set:
            for v in get_vars(integral):
                alpha_delta[v] = BoolVal("True")
            for reset in reset_pool:
                for r in reset:
                    alpha_delta[r] = BoolVal("True")
                max_literal_set, alpha_delta = self.solve_strategy_aux(alpha_delta, psi_abs, i)
                if max_literal_set is not None and alpha_delta is not None:
                    s_diff = set()
                    for se in max_literal_set:
                        if isinstance(se, Bool):
                            if "newTau#" in se.id:
                                s_diff.add(se)
                    max_literal_set = max_literal_set.difference(s_diff)
                    return max_literal_set, alpha_delta

    @abc.abstractmethod
    def solve_strategy_aux(self, alpha_delta, psi_abs, bound):
        pass


class HylaaSolver(BaseSolver, HylaaStrategy, ABC):
    def __init__(self):
        BaseSolver.__init__(self)
        self.hylaa_core = None

    def solve(self, all_consts, info_dict=None):
        if info_dict is None:
            info_dict = dict()
        # result, size, self._hylaa_model = hylaaCheckSat(all_consts, info_dict)
        # pre-processing
        # mode_dict, else_dict = divide_dict(info_dict)
        # 1. Build \varphi_ABS and mapping_info
        solve_start = timer()
        abstraction_set = get_boolean_abstraction(all_consts)
        inverse_mapping_info, inverse_mapping_info_without_and = gen_fresh_new_var_map(abstraction_set)
        abstracted_consts = forall_integral_substitution(all_consts, inverse_mapping_info)
        mapping_info = inverse_dict(inverse_mapping_info_without_and)
        max_bound = get_bound(mapping_info)
        step1_end = timer()

        self.add_step1_time(str(step1_end - solve_start))
        # self.add_log_info("------------------------------")
        hylaa_result = True
        counter_consts = None

        cur_index = 0
        while hylaa_result:
            self.add_loop_time(str(cur_index))
            loop_start = timer()
            cur_index += 1
            if counter_consts is not None:
                abstracted_consts = And([abstracted_consts, Or(counter_consts)])
            # 2. Perform process #2 from note
            solver = Z3Solver()
            result, size = solver.solve(abstracted_consts)

            smt_solving_end = timer()

            self.add_smt_solving_time(str(smt_solving_end - loop_start))

            if result:
                print("Smt solver level result!")
                # self.add_log_info("SMT solver level result!")
                return True, 0
            assignment = solver.make_assignment()
            alpha = assignment.get_assignments()

            net_dict = info_dict.copy()
            net_dict.update(mapping_info)
            new_alpha = gen_net_assignment(alpha, net_dict)
            # new_abstracted_consts = substitution(abstracted_consts, new_alpha)
            new_abstracted_consts = abstracted_consts
            c = clause(new_abstracted_consts)
            s_diff = set()
            for elem in c:
                vs = get_vars(elem)
                if len(vs) == 0:
                    s_diff.add(elem)

            c = c.difference(s_diff)

            max_literal_set_list, alpha_delta = self.solve_strategy(alpha, assignment, max_bound, new_abstracted_consts,
                                                                    c)

            counter_consts_set = set()
            for s in max_literal_set_list:
                for c in s:
                    if str(alpha_delta[c]) == "True":
                        counter_consts_set.add(Not(c))
                    else:
                        counter_consts_set.add(c)
            counter_consts = list(counter_consts_set)

            remove_mode_clauses = list()
            for clause_bound in max_literal_set_list:
                s_diff = set()
                for elem in clause_bound:
                    vs = get_vars(elem)
                    for v in vs:
                        if v in new_alpha:
                            s_diff.add(elem)
                clause_bound = clause_bound.difference(s_diff)
                remove_mode_clauses.append(clause_bound)

            max_literal_set_list = remove_mode_clauses
            solve_strategy_time = timer()

            self.add_literal_set_time(str(solve_strategy_time - smt_solving_end))
            hylaa_start_time = timer()
            try:
                hylaa_result = self.gen_and_run_hylaa_ha(max_literal_set_list, max_bound, mapping_info,
                                                         new_alpha)
                # counter_consts_set = set()
                # for s in max_literal_set_list:
                #     for c in s:
                #         if str(alpha_delta[c]) == "True":
                #             counter_consts_set.add(Not(c))
                #         else:
                #             counter_consts_set.add(c)
                # counter_consts = list(counter_consts_set)

            except RuntimeError as re:
                print("inside error")
                # negate the error state
                hylaa_result = True
                # counter_consts_set = set()
                # for s in max_literal_set_list:
                #     for c in s:
                #         if str(alpha_delta[c]) == "True":
                #             counter_consts_set.add(Not(c))
                #         else:
                #             counter_consts_set.add(c)
                # counter_consts = list(counter_consts_set)
                import sys
                import traceback
                exc_type, exc_value, exc_traceback = sys.exc_info()
                traceback.print_tb(exc_traceback, file=sys.stdout)
                print(repr(re))
            hylaa_end_time = timer()
            self.add_hylaa_time(str(hylaa_end_time - hylaa_start_time))
            self.add_log_info()
            # self.add_log_info("------------------------------")

        # TODO: replace -1 to formula size
        return hylaa_result, -1

    def gen_and_run_hylaa_ha(self, s_f_list, bound, sigma, alpha):
        new_s_f_list = list()
        for s in s_f_list:
            new_s = set()
            for c in s:
                new_s.add(substitution(c, sigma))
            new_s_f_list.append(new_s)

        sv = get_vars_from_set(new_s_f_list)
        l_v = list()
        for v in sv:
            new_v = remove_index(v)
            if new_v.id not in l_v:
                l_v.append(new_v.id)

        ha = HybridAutomaton('ha')
        l_mode = list()
        for i in range(bound + 1):
            l_mode.append(make_mode_property(s_f_list[i], i, bound, l_v, ha, sigma))

        l_mode.append(ha.new_mode("error"))
        for i in range(bound + 1):
            make_transition(s_f_list[i], i, bound, l_v, ha, l_mode[i], l_mode[i + 1])

        forall_set, integral_set, init_set, tau_set, reset_set, guard_set = unit_split(s_f_list[0], bound)

        # assumption: all boundaries should be number
        sympy_expr_list = list()

        for cc in init_set:
            # if not isinstance(cc, Lt) or not isinstance(cc, Leq) or \
            #         not isinstance(cc, Gt) or not isinstance(cc, Geq) or \
            #         not isinstance(cc, Eq) or not isinstance(cc, Neq):
            sympy_expr_list.append(simplify(expr_to_sympy(reduce_not(cc))))

        bound_box_list = list()
        for i in range(len(l_v)):
            bound_box_list.append([None, None])

        for t in l_v:
            if "tau" in t:
                index = find_index(l_v, Real(t))
                bound_box_list[index][0] = Float(0.0)
                bound_box_list[index][1] = Float(0.0)

        for expr in sympy_expr_list:
            if isinstance(expr, GreaterThan) or isinstance(expr, StrictGreaterThan):
                # left is variable
                if isinstance(expr.lhs, Symbol):
                    var_id = str(expr.lhs)
                    index = find_index(l_v, Real(var_id))
                    if bound_box_list[index][0] is None:
                        bound_box_list[index][0] = expr.rhs
                    else:
                        if str(simplify(bound_box_list[index][0] <= expr.rhs)) == "True":
                            bound_box_list[index][0] = expr.rhs
                else:
                    var_id = str(expr.rhs)
                    index = find_index(l_v, Real(var_id))
                    if bound_box_list[index][1] is None:
                        bound_box_list[index][1] = expr.lhs
                    else:
                        if str(simplify(bound_box_list[index][1] <= expr.lhs)) == "True":
                            bound_box_list[index][1] = expr.lhs

            elif isinstance(expr, LessThan) or isinstance(expr, StrictLessThan):
                # left is variable
                if isinstance(expr.lhs, Symbol):
                    var_id = str(expr.lhs)
                    index = find_index(l_v, Real(var_id))
                    if bound_box_list[index][1] is None:
                        bound_box_list[index][1] = expr.rhs
                    else:
                        if str(simplify(bound_box_list[index][1] >= expr.rhs)) == "True":
                            bound_box_list[index][1] = expr.rhs
                else:
                    var_id = str(expr.rhs)
                    index = find_index(l_v, Real(var_id))
                    if bound_box_list[index][0] is None:
                        bound_box_list[index][0] = expr.lhs
                    else:
                        if str(simplify(bound_box_list[index][0] >= expr.lhs)) == "True":
                            bound_box_list[index][0] = expr.lhs
        new_bound_box_list = list()
        for e in bound_box_list:
            bound_box_left = -float("inf")
            bound_box_right = float("inf")
            if e[0] is not None:
                bound_box_left = float(e[0])
            if e[1] is not None:
                bound_box_right = float(e[1])
            new_bound_box_list.append([bound_box_left, bound_box_right])

        # add affine variable
        new_bound_box_list.append([1.0, 1.0])
        mode = ha.modes['mode0']
        init_lpi = lputil.from_box(new_bound_box_list, mode)
        init_list = [StateSet(init_lpi, mode)]
        settings = HylaaSettings(0.01, 100)
        # settings.stop_on_aggregated_error = False
        settings.aggstrat.deaggregate = True  # use deaggregation
        core = Core(ha, settings)
        ce = core.run(init_list)
        # self.add_log_info(str(ce.counterexample))
        if core.is_counterexample:
            self.hylaa_core = core
            return False
        else:
            return True

    def make_assignment(self):
        if self.hylaa_core is not None:
            return HylaaAssignment(self.hylaa_core.get_counterexample())
        return HylaaAssignment(None)


class HylaaSolverNaive(HylaaSolver):
    def __init__(self):
        super(HylaaSolver, self).__init__()

    def solve_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c):
        return self.get_max_literal(alpha, assignment, max_bound, new_abstracted_consts, c)

    def solve_strategy_aux(self, alpha_delta, psi_abs, bound):
        solver = Z3Solver()
        # print(solver.simplify(solver.substitution(reduce_not(psi_abs), alpha_delta)))
        sub_dict = {}
        for c in alpha_delta:
            if str(alpha_delta[c]) == "True":
                sub_dict[c] = BoolVal("True")
                if not isinstance(c, Bool):
                    sub_dict[reduce_not(Not(c))] = BoolVal("False")
            else:
                sub_dict[c] = BoolVal("False")
                if not isinstance(c, Bool):
                    sub_dict[reduce_not(Not(c))] = BoolVal("True")

        simplified_result = solver.simplify(solver.substitution(reduce_not(psi_abs), sub_dict))

        s_abs_set = set()

        if str(simplified_result) == "True":
            for c in alpha_delta:
                b_forall, b_integral, b_zero, b_tau, b_reset, b_guard = unit_split({c}, bound)
                if (len(b_forall) == 1 or len(b_integral) == 1 or len(b_zero) == 1 or
                        len(b_tau) == 1 or len(b_reset) == 1 or len(b_guard) == 1):
                    if str(alpha_delta[c]) == 'True' and not isinstance(c, Neq):
                        s_abs_set.add(c)

            return s_abs_set, alpha_delta
        else:
            return None, alpha_delta


class HylaaSolverReduction(HylaaSolver):
    def __init__(self):
        super(HylaaSolver, self).__init__()

    def solve_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c):
        return self.get_max_literal(alpha, assignment, max_bound, new_abstracted_consts, c)

    def solve_strategy_aux(self, alpha_delta, psi_abs, bound):
        solver = Z3Solver()
        simplified_result = solver.simplify(solver.substitution(reduce_not(psi_abs), alpha_delta))
        s_abs_set = set()

        if str(simplified_result) == "True":
            for c in alpha_delta:
                b_forall, b_integral, b_zero, b_tau, b_reset, b_guard = unit_split({c}, bound)
                if (len(b_forall) == 1 or len(b_integral) == 1 or len(b_zero) == 1 or
                        len(b_tau) == 1 or len(b_reset) == 1 or len(b_guard) == 1):
                    if str(alpha_delta[c]) == 'True' and not isinstance(c, Not):
                        s_abs_set.add(c)

            return self.delta_debugging(s_abs_set, psi_abs), alpha_delta
        else:
            return None, alpha_delta

    def delta_debugging_aux(self, c_max: set, psi: Constraint):
        if len(c_max) == 0:
            return set()
        alpha = dict()
        for c in c_max:
            alpha[c] = BoolVal("True")

        for c in c_max:
            new_alpha = alpha.copy()
            new_alpha[c] = BoolVal("False")
            solver = Z3Solver()
            simplified_result = solver.simplify(solver.substitution(psi, new_alpha))

            if str(simplified_result) == "True":
                return self.delta_debugging_aux(c_max.difference({c}), psi).union({c})

        return set()

    def delta_debugging(self, c_max, psi):
        s = self.delta_debugging_aux(c_max, psi)
        return c_max.difference(s)


class HylaaSolverMultiJump(HylaaSolver):
    def __init__(self):
        super(HylaaSolver, self).__init__()

    def solve_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c):
        c_sat = set()
        c_unsat = set()
        total = dict()
        for c_elem in c:
            vs = get_vars(c_elem)
            flag = True

            for c_vs in vs:
                if "chi" in c_vs.id or "newIntegral" in c_vs.id or "newTau" in c_vs.id or (
                        c_vs.id.count('_') == 1 and ('tau' not in c_vs.id)):
                    flag = False
                    if c_vs not in alpha:
                        total[c_vs] = BoolVal("True")
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
                    total[reduce_not(Not(c_elem))] = BoolVal("True")
                    c_unsat.add(Not(c_elem))

        c = self.apply_unsat_core(c, new_abstracted_consts, assignment)
        max_literal_set_list = list()
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
                new_set.add(reduce_not(cc))
            max_literal_set_list.append(new_set)
        return max_literal_set_list, total

    def solve_strategy_aux(self, alpha_delta, psi_abs, bound):
        pass

    def apply_unsat_core(self, c_max, psi, assignment: Assignment):
        c_sat = set()
        c_unsat = set()

        for c in c_max:
            if assignment.eval(c):
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
        return solver.unsat_core(psi, assertion_and_trace)


class HylaaSolverUnsatCore(HylaaSolver):
    def __init__(self):
        super(HylaaSolver, self).__init__()

    def solve_strategy(self, alpha, assignment, max_bound, new_abstracted_consts, c):
        c_sat = set()
        c_unsat = set()
        total = dict()
        for c_elem in c:
            vs = get_vars(c_elem)
            flag = True

            for c_vs in vs:
                if "chi" in c_vs.id or "newIntegral" in c_vs.id or (c_vs.id.count('_') == 1 and 'tau' not in c_vs.id):
                    flag = False
                    if c_vs not in alpha:
                        total[c_vs] = BoolVal("True")
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
                    total[reduce_not(Not(c_elem))] = BoolVal("True")
                    c_unsat.add(Not(c_elem))

        c = self.apply_unsat_core(c, new_abstracted_consts, assignment)
        max_literal_set_list = list()
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
                new_set.add(reduce_not(cc))
            s_diff = set()
            for se in new_set:
                if isinstance(se, Bool):
                    if "newTau#" in se.id:
                        s_diff.add(se)
            new_set = new_set.difference(s_diff)
            max_literal_set_list.append(new_set)
        return max_literal_set_list, total

    def solve_strategy_aux(self, alpha_delta, psi_abs, bound):
        pass

    def apply_unsat_core(self, c_max, psi, assignment: Assignment):
        c_sat = set()
        c_unsat = set()

        for c in c_max:
            if assignment.eval(c):
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
        return solver.unsat_core(psi, assertion_and_trace)


class HylaaAssignment(Assignment):
    def __init__(self, hylaa_counterexample):
        self.hylaa_counterexample = hylaa_counterexample

    def get_assignments(self):
        print(self.hylaa_counterexample)

    def eval(self, const):
        pass


def make_reset_pool(s_i_reset):
    s_i_pool = list()
    s_v = set()
    for c in s_i_reset:
        s_v = s_v.union(get_vars(c.left))

    s_i_r = s_i_reset
    s_diff = set()

    for v in s_v:
        s_l = set()
        for c in s_i_r:
            if c.left.id == v.id:
                s_l.add(c)
                s_diff.add(c)
        s_i_r = s_i_r.difference(s_diff)
        s_i_pool.append(s_l)

    tuple_to_set = list(product(*s_i_pool))
    s_i_pool = list()
    for i in tuple_to_set:
        chi = [element for tupl in i for element in (tupl if isinstance(tupl, tuple) else (tupl,))]
        s_i_pool.append(set(chi))

    return s_i_pool


@singledispatch
def get_string(const: Constraint):
    return {const}


@get_string.register(Variable)
def _(const: Variable):
    start_index = int(const.id.find("_"))
    return {const.id[:start_index]}


def revert_by_sigma(clauses: set, sigma: dict):
    revert_s = set()
    for c in clauses:
        if c in sigma:
            revert_s.add(sigma[c])
        else:
            revert_s.add(c)
    return revert_s


@singledispatch
def sympy_var(expr: relational):
    raise NotSupportedError("cannot make box : " + str(expr))


@sympy_var.register(Symbol)
def _(expr: Symbol):
    return expr


@singledispatch
def sympy_value(expr: relational):
    raise NotSupportedError("cannot make box : " + str(expr))


@sympy_value.register(Float)
def sympy_value(expr: Float):
    return expr


@singledispatch
def expr_to_sympy(const: Constraint):
    raise NotSupportedError("cannot make it canonical : " + str(const))


@expr_to_sympy.register(Variable)
def _(const: Variable):
    return symbols(const.id)


@expr_to_sympy.register(Constant)
def _(const: Constant):
    return float(const.value)


@expr_to_sympy.register(Add)
def _(const: Add):
    return expr_to_sympy(const.left) + expr_to_sympy(const.right)


@expr_to_sympy.register(Sub)
def _(const: Sub):
    return expr_to_sympy(const.left) - expr_to_sympy(const.right)


@expr_to_sympy.register(Mul)
def _(const: Mul):
    return expr_to_sympy(const.left) * expr_to_sympy(const.right)


@expr_to_sympy.register(Div)
def _(const: Div):
    return expr_to_sympy(const.left) / expr_to_sympy(const.right)


@expr_to_sympy.register(Pow)
def _(const: Pow):
    return expr_to_sympy(const.left) ** expr_to_sympy(const.right)


@expr_to_sympy.register(Gt)
def _(const: Gt):
    return StrictGreaterThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Geq)
def _(const: Geq):
    return GreaterThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Lt)
def _(const: Lt):
    return StrictLessThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Leq)
def _(const: Leq):
    return LessThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Eq)
def _(const: Eq):
    return Equality(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Neq)
def _(const: Neq):
    return Unequality(expr_to_sympy(const.left), expr_to_sympy(const.right))


@singledispatch
def remove_index(c: Constraint) -> Variable:
    raise NotSupportedError("input should be variable type : " + str(c))


@remove_index.register(Variable)
def _(v: Variable) -> Variable:
    if "tau" not in v.id:
        start_index = v.id.find("_")
        var_id = v.id[:start_index]
        return Real(var_id)
    return v


def get_vars_from_set(set_of_list: list):
    result_set = set()
    for s in set_of_list:
        for c in s:
            result_set = result_set.union(get_vars(c))
    return result_set


def find_index(input_list: list, v: Variable):
    index = 0
    for e in input_list:
        if e in v.id:
            return index
        index += 1
    raise NotFoundElementError(v, "index not found")


def make_mode_property(s_psi_abs_i, i, max_bound, l_v, ha: HybridAutomaton, sigma):
    mode_i = ha.new_mode("mode" + str(i))
    s_forall_i, s_integral_i, s_0, s_tau_i, s_reset_i, s_guard_i = unit_split(s_psi_abs_i, i)
    l_integral = l_v.copy()

    for integral in s_integral_i:
        index = 0
        for exp in sigma[integral].dynamics.exps:
            try:
                k = find_index(l_v, sigma[integral].dynamics.vars[index])
                l_integral[k] = infix(exp)
                index += 1
            except NotFoundElementError as ne:
                print(ne)
                raise NotSupportedError("element should be found!")

    for j in range(i + 1):
        k_j = find_index(l_v, Real("tau_" + str(j)))
        l_integral[k_j] = "0"

    for j in range(i + 1, max_bound + 2):
        k_j = find_index(l_v, Real("tau_" + str(j)))
        l_integral[k_j] = "1"
    m_integral = symbolic.make_dynamics_mat(l_v, l_integral, {}, has_affine_variable=True)
    mode_i.set_dynamics(m_integral)

    phi_forall_children = list()
    for c in s_forall_i:
        new_c = substitution(c, sigma)
        vs = get_vars(new_c)
        new_dict = dict()
        for v in vs:
            new_dict[v] = remove_index(v)
        phi_forall_children.append(reduce_not(substitution(new_c, new_dict)))

    if len(phi_forall_children) > 0:
        m_forall, m_forall_rhs = symbolic.make_condition(l_v, infix(And(phi_forall_children)).split('&'), {},
                                                         has_affine_variable=True)
        mode_i.set_invariant(m_forall, m_forall_rhs)
    return mode_i


def make_transition(s_psi_abs_i, i, max_bound, l_v, ha: HybridAutomaton, mode_p, mode_n):
    trans_i = ha.new_transition(mode_p, mode_n)
    s_forall_i, s_integral_i, s_0, s_tau_i, s_reset_i, s_guard_i = unit_split(s_psi_abs_i, i)

    guard_i_children = list(s_guard_i)
    tau_i_children = list(s_tau_i)
    total_children = list()

    total_children.extend(guard_i_children)
    total_children.extend(tau_i_children)

    phi_reset_children = list()
    for c in total_children:
        vs = get_vars(c)
        new_dict = dict()
        for v in vs:
            new_dict[v] = remove_index(v)
        phi_reset_children.append(reduce_not(substitution(c, new_dict)))

    # print("suu")
    # for ssss in infix(And(phi_reset_children)).split('&'):
    #     print(ssss)
    # print(infix(And(phi_reset_children)).split('&'))
    m_guard, m_guard_rhs = symbolic.make_condition(l_v, infix(And(phi_reset_children)).split('&'), {},
                                                   has_affine_variable=True)
    trans_i.set_guard(m_guard, m_guard_rhs)

    remove_var_dict = dict()
    for c in s_reset_i:
        vs = get_vars(c)
        for v in vs:
            remove_var_dict[v] = remove_index(v)

    l_r = l_v.copy()
    for r in s_reset_i:
        k = find_index(l_v, r.left)
        l_r[k] = infix(substitution(r.right, remove_var_dict))

    if "tau" in l_v:
        for j in range(max_bound + 1):
            k_t_j = find_index(l_v, Real("tau_" + str(j)))
            l_r[k_t_j] = "tau_" + str(j)

    reset_mat = symbolic.make_reset_mat(l_v, l_r, {}, has_affine_variable=True)
    trans_i.set_reset(reset_mat)


def z3_bool_to_const_bool(z3list):
    return [Bool(str(b)) for b in z3list]


def get_bound(mapping_info: dict):
    max_bound = -1
    for key in mapping_info:
        # for forall
        index = int(key.id.rfind("_")) + 1
        bound = int(key.id[index:])
        if max_bound < bound:
            max_bound = bound
    return max_bound


def gen_sigma(s: set, op: str):
    sigma = dict()
    index = 0
    for c in s:
        v = Bool("new#" + str(index) + op)
        sigma[v] = c
        index += 1
    return sigma


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
        for var in var_set:
            start_index = int(var.id.find("_"))
            if var.id[start_index:] == "_0_0" and "newIntegral" not in var.id and "invAtomicID" not in var.id:
                init_set.add(c)
                s_diff.add(c)
                break

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        var_set = get_vars(c)
        for var in var_set:
            start_index = int(var.id.find("#"))
            s_index = int(var.id.find("_"))
            e_index = int(var.id.rfind("_"))
            bound_index = int(var.id.rfind("_"))
            if not (s_index == -1) and ((s_index == e_index and "tau" not in var.id)
                                        or ("invAtomicID" in var.id) or ("newPropDecl" in var.id)):
                bound = int(var.id[bound_index + 1:])
                if i == bound:
                    forall_set.add(c)
                    s_diff.add(c)
                    break
            elif var.id[:start_index] == "newIntegral":
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
            if "newTau#" in c.id and int(c.id[-1]) == i:
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
                    or "newPropDecl" in var.id or "newTau" in var.id):
                bound = int(var.id[start_index + 1:end_index])
                last_str = var.id[-1]
                if not ((bound == i and last_str == "t") or (bound == i + 1 and last_str == "0")):
                    flag = False
                if isinstance(c.left, Real):
                    if c.left.id[e_index + 1:] == "0":
                        flag = False
                        break
            else:
                flag = False
        if flag:
            guard_set.add(c)
            s_diff.add(c)

    return forall_set, integral_set, init_set, tau_set, reset_set, guard_set


def gen_net_assignment(mapping: dict, range_dict: dict):
    new_dict = dict()
    for var in mapping:
        search_index = var.id.find("_")
        search_id = var.id[:search_index]
        if not (Bool(var.id) in range_dict or Real(search_id) in range_dict or Real(
                var.id) in range_dict or "tau" in var.id):
            new_dict[var] = mapping[var]
    return new_dict


@singledispatch
def gen_fresh_new_var_map_aux(const: Constraint, id_str=None):
    raise NotSupportedError("cannot create mapping for integral and forall : " + str(const) + ", " + str(id_str))


@gen_fresh_new_var_map_aux.register(Integral)
def _(const: Integral):
    new_map = dict()
    new_map_without_and = dict()
    end_var_str = const.end_vector[0].id
    start_index = end_var_str.find('_')
    bound_str = end_var_str[start_index + 1:-2]
    new_id = "newIntegral#_" + str(const.current_mode_number) + "_" + bound_str
    new_map[const] = Bool(new_id)
    new_map_without_and[const] = Bool(new_id)
    return new_map, new_map_without_and


@gen_fresh_new_var_map_aux.register(Forall)
def _(const: Forall):
    new_map = dict()
    new_map_without_and = dict()
    end_var_str = const.integral.end_vector[0].id
    start_index = end_var_str.find('_')
    bound_str = end_var_str[start_index + 1:-2]
    new_id = "newForall#" + str(id(const)) + "_" + str(const.current_mode_number) + "_" + bound_str
    new_map[const] = And([Bool(new_id), const.const])
    new_map_without_and[const] = Bool(new_id)
    return new_map, new_map_without_and


@gen_fresh_new_var_map_aux.register(Eq)
def _(const: Eq):
    new_map = dict()
    new_map_without_and = dict()
    flag = False
    # const_key is Forall object, const_value is boolean variable id
    if isinstance(const.left, Forall) or isinstance(const.right, Forall):
        flag = True
    if isinstance(const.left, Forall):
        const_key = const.left
        const_value = const.right
    else:
        const_key = const.right
        const_value = const.left

    if flag:
        new_map[const] = BoolVal("True")
    new_map_without_and[const_key] = const_value
    return new_map, new_map_without_and


def gen_fresh_new_var_map(if_set: set):
    new_map = dict()
    new_map_without_and = dict()
    for elem in if_set:
        m, nm = gen_fresh_new_var_map_aux(elem)
        new_map.update(m)
        new_map_without_and.update(nm)
    return new_map, new_map_without_and


def divide_dict(info_dict: dict):
    mode_dict = dict()
    else_dict = dict()
    for key in info_dict:
        if isinstance(key, str):
            mode_dict[key] = info_dict[key]
        else:
            else_dict[key] = info_dict[key]
    return mode_dict, else_dict


@singledispatch
def clause(const: Constraint):
    return {const}


@clause.register(Not)
def _(const: Not):
    return clause(const.child)


@clause.register(And)
def _(const: And):
    result = set()
    for c in list(const.children):
        result = result.union(clause(c))
    return result


@clause.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Formula):
        return clause(const.left).union(clause(const.right))
    return {const}


@clause.register(Or)
def _(const: Or):
    result = set()
    for c in list(const.children):
        result = result.union(clause(c))
    return result


@clause.register(Not)
def _(const: Not):
    result = set()
    return result.union(clause(const.child))


@clause.register(Implies)
def _(const):
    result = set()
    result = result.union(clause(const.left))
    result = result.union(clause(const.right))
    return result
