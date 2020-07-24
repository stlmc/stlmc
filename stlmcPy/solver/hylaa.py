from abc import ABC
from functools import singledispatch
from itertools import product

from hylaa import symbolic
from hylaa.hybrid_automaton import HybridAutomaton
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_integrals_and_foralls, inverse_dict, \
    forall_integral_substitution, substitution, reduce_not, get_vars
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.abstract_solver import BaseSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.z3 import Z3Solver
import abc


class HylaaStrategy:

    @abc.abstractmethod
    def solve_strategy(self, alpha_delta, psi_abs):
        pass


class BaseHylaaSolver(BaseSolver, HylaaStrategy, ABC):
    def __init__(self):
        self._hylaa_model = None

    def solve(self, all_consts, info_dict=None):
        if info_dict is None:
            info_dict = dict()
        # result, size, self._hylaa_model = hylaaCheckSat(all_consts, info_dict)
        # pre-processing
        # mode_dict, else_dict = divide_dict(info_dict)
        # 1. Build \varphi_ABS and mapping_info
        integral_forall_set = get_integrals_and_foralls(all_consts)
        inverse_mapping_info = gen_fresh_new_var_map(integral_forall_set)
        abstracted_consts = forall_integral_substitution(all_consts, inverse_mapping_info)
        mapping_info = inverse_dict(inverse_mapping_info)
        max_bound = get_bound(mapping_info)

        # print(abstracted_consts)
        # 2. Perform process #2 from note
        solver = Z3Solver()
        result, size = solver.solve(abstracted_consts)

        if result:
            return True, 0, None
        assignment = solver.make_assignment()
        alpha = assignment.get_assignments()

        net_dict = info_dict.copy()
        net_dict.update(mapping_info)
        new_alpha = gen_net_assignment(alpha, net_dict)
        new_abstracted_consts = substitution(abstracted_consts, new_alpha)
        c = clause(new_abstracted_consts)
        c_sat = set()
        c_unsat = set()
        total = dict()
        for c_elem in c:
            if assignment.eval(c_elem):
                c_sat.add(c_elem)
                total[c_elem] = BoolVal("True")
            else:
                c_unsat.add(Not(c_elem))
                total[c_elem] = BoolVal("False")


        # S = c_sat.union(c_unsat)


        # solver = Z3Solver()
        # simplified_result = solver.simplify(solver.substitution(new_abstracted_consts, total))
        # print(simplified_result)
        for i in range(max_bound + 1):
            self.get_max_literal(new_abstracted_consts, i, c_sat, total)
        return None, 0
        # return result, size

    def get_max_literal(self, psi_abs, i, c_sat, alpha_delta: dict):
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
                max_literal_set = self.solve_strategy(alpha_delta, psi_abs)
                if max_literal_set is not None:
                    return max_literal_set

    def make_assignment(self):
        return HylaaAssignment(self._hylaa_model)


class HylaaSolver(BaseHylaaSolver):
    def __init__(self):
        super(HylaaSolver, self).__init__()

    def solve_strategy(self, alpha_delta, psi_abs):
        solver = Z3Solver()
        simplified_result = solver.simplify(solver.substitution(psi_abs, alpha_delta))
        print(simplified_result)
        s_abs_set = set()
        if str(simplified_result) == "True":
            for c in alpha_delta:
                if alpha_delta[c].value == "True":
                    s_abs_set.add(c)
            return s_abs_set
        else:
            return None




class HylaaAssignment(Assignment):
    def __init__(self, p):
        pass

    def get_assignments(self):
        pass


# def hylaaCheckSat(all_consts, info_dict):
#     # pre-processing
#     # mode_dict, else_dict = divide_dict(info_dict)
#     # 1. Build \varphi_ABS and mapping_info
#     integral_forall_set = get_integrals_and_foralls(all_consts)
#     inverse_mapping_info = gen_fresh_new_var_map(integral_forall_set)
#     abstracted_consts = forall_integral_substitution(all_consts, inverse_mapping_info)
#     mapping_info = inverse_dict(inverse_mapping_info)
#     max_bound = get_bound(mapping_info)
#
#     # print(abstracted_consts)
#     # 2. Perform process #2 from note
#     solver = Z3Solver()
#     result, size = solver.solve(abstracted_consts)
#
#     if result:
#         return True, 0, None
#     assignment = solver.make_assignment()
#     alpha = assignment.get_assignments()
#
#     net_dict = info_dict.copy()
#     net_dict.update(mapping_info)
#     new_alpha = gen_net_assignment(alpha, net_dict)
#     new_abstracted_consts = substitution(abstracted_consts, new_alpha)
#     c = clause(new_abstracted_consts)
#     # c_sat = set()
#     # c_unsat = set()
#     # for c_elem in c:
#     #     if assignment.eval(c_elem):
#     #         c_sat.add(c_elem)
#     #     else:
#     #         c_unsat.add(Not(c_elem))
#     # S = c_sat.union(c_unsat)
#
#     # S = set()
#     # for var in alpha:
#     #     if var.type == 'bool' and alpha[var].value == 'True':
#     #         S.add(var)
#     #     elif var.type == 'bool' and alpha[var].value == 'False':
#     #         S.add(Not(var))
#     #     else:
#     #         S.add(Eq(var, alpha[var]))
#
#     # print(alpha)
#     # print(S)
#
#     # 3. Use algorithm2 in stlmc_algorithm.
#     union_forall_set, union_integral_set, init_set, union_tau_set, union_reset_set, union_guard_set = split(c,
#                                                                                                             max_bound)
#     psi_consts = new_abstracted_consts
#     c_sat = set()
#     c_unsat = set()
#     init_sigma = gen_sigma(init_set, "initCondition")
#     inverse_sigma = inverse_dict(init_sigma)
#     for i in range(max_bound + 1):
#         sigma_guard = gen_sigma(union_guard_set[i], "sigmaGuard_" + str(i))
#         sigma_reset = gen_sigma(union_reset_set[i], "sigmaReset_" + str(i))
#         sigma_tau = gen_sigma(union_tau_set[i], "sigmaTau_" + str(i))
#         if i == max_bound:
#             sigma_tau.update(gen_sigma(union_tau_set[i + 1], "sigmaTau_" + str(i + 1)))
#         new_sigma = dict()
#         new_sigma.update(sigma_guard)
#         new_sigma.update(sigma_reset)
#         new_sigma.update(sigma_tau)
#         inverse_sigma.update(inverse_dict(new_sigma))
#         psi_consts = substitution(psi_consts, inverse_sigma)
#         inverse_sigma.update(inverse_dict(new_sigma))
#         for key in inverse_sigma:
#             if assignment.eval(key):
#                 c_sat.add(inverse_sigma[key])
#             else:
#                 c_unsat.add(Not(inverse_sigma[key]))
#
#     for var in alpha:
#         if ("newIntegral" in var.id or "newForall" in var.id) and alpha[var] == BoolVal("True"):
#             c_sat.add(var)
#         elif ("newIntegral" in var.id or "newForall" in var.id) and alpha[var] == BoolVal("False"):
#             c_unsat.add(Not(var))
#
#     c_total = c_sat.union(c_unsat)
#     new_solver = Z3Solver()
#     s_prime = new_solver.unsat_core(Not(psi_consts), list(c_total))
#     s_f_prime = set()
#     original_sigma = inverse_dict(inverse_sigma)
#     for c in z3_bool_to_const_bool(s_prime):
#         if not (c in original_sigma):
#             s_f_prime.add(c)
#         else:
#             s_f_prime.add(original_sigma[c])
#
#     # print(s_f_prime)
#     # # revert integral and forall from s_f_prime
#     # revert_s_f_prime = set()
#     # for c in s_f_prime:
#     #     if c in mapping_info:
#     #         revert_s_f_prime.add(mapping_info[c])
#     #     else:
#     #         revert_s_f_prime.add(c)
#
#     # print(revert_s_f_prime)
#
#     gen_hylaa_ha(s_f_prime, max_bound, mapping_info)
#
#     return False, 0, None


# @singledispatch
# def get_string(const: set):
#     var_id_list = list()
#     for e in const:
#         var_id_list.extend(get_string(e))
#     return var_id_list


# @singledispatch
# def get_string(const: set):
#     var_id_list = list()
#     for e in const:
#         var_id_list.extend(get_string(e))
#     return var_id_list


def make_reset_pool(s_i_reset):
    s_i_pool = set()
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
        if len(s_i_pool) == 0:
            s_i_pool = s_l
        else:
            s_i_pool = set(product(s_i_pool, s_l))
    return s_i_pool


@singledispatch
def get_string(const: Constraint):
    return {const}


@get_string.register(Variable)
def _(const: Variable):
    start_index = int(const.id.find("_"))
    return {const.id[:start_index]}


# @get_string.register(Integral)
# def _(const: Integral):
#
#     for exp in const.dynamics.exps:
#         exp_set.add(set(exp))
#     return exp_set


def revert_by_sigma(clauses: set, sigma: dict):
    revert_s = set()
    for c in clauses:
        if c in sigma:
            revert_s.add(sigma[c])
        else:
            revert_s.add(c)
    return revert_s


def get_variable_vector(union_integral_set, max_bound, mapping_info):
    var_set = set()
    for i in range(max_bound):
        # since this is singleton set
        integrals = revert_by_sigma(union_integral_set[i], mapping_info)
        for integral in integrals:
            # print(get_vars(integral))
            for var in integral.vars:
                var_set = var_set.union(get_string(var))
    # print(var_set)
    return var_set


def gen_hylaa_ha(s_f_prime, max_bound, mapping_info):
    # union_forall_set, union_integral_set, init_set, union_tau_set, union_reset_set, union_guard_set = split(s_f_prime,max_bound)

    # revert integral and forall from s_f_prime
    # revert_integral_set = list()
    # var_list = list()
    # var_set = get_variable_vector(union_integral_set, max_bound, mapping_info)
    # var_list = list(var_set)

    # print(var_list)

    # print(get_string(revert_integral_set[0]))
    # print(union_forall_set)
    # print(get_string(union_integral_set[0]))
    # ha = HybridAutomaton('habrid_automata')
    # for i in range(max_bound + 1):
    #     if i == max_bound:
    #         pass
    #     else:
    #         mode = ha.new_mode("mode" + str(i))
    #         integral = list(revert_by_sigma(union_integral_set[i], mapping_info))[0]
    #         derivatives = list()
    #         get_infix_string(integral.dynamics.exps)
    #         a_mat = symbolic.make_dynamics_mat(var_list, derivatives, {}, has_affine_variable=True)
    #         mode.set_dynamics(a_mat)
    return None


def z3_bool_to_const_bool(z3list):
    return [Bool(str(b)) for b in z3list]


def get_bound(mapping_info: dict):
    max_bound = -1
    for key in mapping_info:
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


def unit_split(S: set, i: int):
    forall_set = set()
    integral_set = set()
    tau_set = set()
    guard_set = set()
    reset_set = set()
    init_set = set()

    S_diff = set()

    for c in S:
        var_set = get_vars(c)
        for var in var_set:
            start_index = int(var.id.find("_"))
            if var.id[start_index:] == "_0_0" and not ("newIntegral" in var.id) and not ("newForall" in var.id):
                init_set.add(c)
                S_diff.add(c)
                break

    S = S.difference(S_diff)
    S_diff = set()

    for c in S:
        var_set = get_vars(c)
        for var in var_set:
            start_index = int(var.id.find("#"))
            bound_index = int(var.id.rfind("_"))
            if var.id[:start_index] == "newForall":
                bound = int(var.id[bound_index + 1:])
                if i == bound:
                    forall_set.add(c)
                    S_diff.add(c)
                    break
            elif var.id[:start_index] == "newIntegral":
                bound = int(var.id[bound_index + 1:])
                if i == bound:
                    integral_set.add(c)
                    S_diff.add(c)
                    break

    S = S.difference(S_diff)
    S_diff = set()

    for c in S:
        var_set = get_vars(c)
        max_bound = -1
        for var in var_set:
            start_index = int(var.id.find("_"))
            if var.id[:start_index] == "tau":
                bound = int(var.id[start_index + 1:])
                if max_bound < bound:
                    max_bound = bound
        if max_bound != -1 and max_bound == i:
            tau_set.add(c)
            S_diff.add(c)

    S = S.difference(S_diff)
    S_diff = set()

    for c in S:
        if isinstance(c, Eq):
            if isinstance(c.left, Variable):
                start_index = int(c.left.id.find("_"))
                end_index = int(c.left.id.rfind("_"))
                bound = int(c.left.id[start_index + 1:end_index])
                if c.left.id[end_index + 1:] == "0" and bound == i + 1:
                    reset_set.add(c)
                    S_diff.add(c)

    S = S.difference(S_diff)
    S_diff = set()

    for c in S:
        var_set = get_vars(c)
        for var in var_set:
            start_index = int(var.id.find("_"))
            end_index = int(var.id.rfind("_"))
            if not ("newForall" in var.id or "newIntegral" in var.id or "tau" in var.id):
                bound = int(var.id[start_index + 1:end_index])
                if bound == i:
                    guard_set.add(c)
                    S_diff.add(c)
                    break

    return forall_set, integral_set, init_set, tau_set, reset_set, guard_set


def gen_net_assignment(mapping: dict, range_dict: dict):
    new_dict = dict()
    for var in mapping:
        search_index = var.id.find("_")
        search_id = var.id[:search_index]
        if not (Real(search_id) in range_dict or Real(var.id) in range_dict or "tau" in var.id):
            new_dict[var] = mapping[var]
    return new_dict


@singledispatch
def gen_fresh_new_var_map_aux(const: Constraint, id_str=None):
    raise NotSupportedError("cannot create mapping for integral and forall")


@gen_fresh_new_var_map_aux.register(Integral)
def _(const: Integral):
    new_map = dict()
    end_var_str = const.end_vector[0].id
    start_index = end_var_str.find('_')
    bound_str = end_var_str[start_index + 1:-2]
    new_id = "newIntegral#_" + str(const.current_mode_number) + "_" + bound_str
    new_map[const] = Bool(new_id)
    return new_map


@gen_fresh_new_var_map_aux.register(Forall)
def _(const: Forall):
    new_map = dict()
    end_var_str = const.integral.end_vector[0].id
    start_index = end_var_str.find('_')
    bound_str = end_var_str[start_index + 1:-2]
    new_id = "newForall#" + str(id(const)) + "_" + str(const.current_mode_number) + "_" + bound_str
    new_map[const] = Bool(new_id)
    return new_map


def gen_fresh_new_var_map(if_set: set, id=None):
    new_map = dict()
    for elem in if_set:
        new_map.update(gen_fresh_new_var_map_aux(elem))
    return new_map


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


@clause.register(And)
def _(const: And):
    result = set()
    for c in list(const.children):
        result = result.union(clause(c))
    return result


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

# # TODO : Should cover Yices and Z3 without notice
# def make_c_sat_with_z3(z3_solver_model, clause_list: list):
#     return [x for x in clause_list if z3_solver_model.eval(z3Obj(x, True))]
#
#
# def make_c_unsat_with_z3(z3_solver_model, clause_list: list):
#     return [Not(x) for x in clause_list if not z3_solver_model.eval(z3Obj(x, True))]

# @singledispatch
# def is_integral_forall(const: Constraint):
#     return False
#
# @is_integral_forall.register(Integral)
# def _(const: Integral):
#     return True
#
# @is_integral_forall.register(Forall)
# def _(const: Forall):
#     return True
#
#
#
# @singledispatch
# def remove_integral_forall(const: Constraint, result_list: list):
#     return const, result_list
#
#
# @remove_integral_forall.register(Unary)
# def _(const: Unary, result_list: list):
#     return
#
# @remove_integral_forall.register(Binary)
#
#
# @remove_integral_forall.register(Multinary)
