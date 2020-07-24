from functools import singledispatch

from hylaa.hybrid_automaton import HybridAutomaton
from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_integrals_and_foralls, inverse_dict, \
    forall_integral_substitution, substitution, reduce_not, get_vars
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.abstract_solver import BaseSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.z3 import Z3Solver


def hylaaCheckSat(all_consts, info_dict):
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
    # c_sat = set()
    # c_unsat = set()
    # for c_elem in c:
    #     if assignment.eval(c_elem):
    #         c_sat.add(c_elem)
    #     else:
    #         c_unsat.add(Not(c_elem))
    # S = c_sat.union(c_unsat)

    # S = set()
    # for var in alpha:
    #     if var.type == 'bool' and alpha[var].value == 'True':
    #         S.add(var)
    #     elif var.type == 'bool' and alpha[var].value == 'False':
    #         S.add(Not(var))
    #     else:
    #         S.add(Eq(var, alpha[var]))


    # print(alpha)
    # print(S)







    # 3. Use algorithm2 in stlmc_algorithm.
    union_forall_set, union_integral_set, init_set, union_tau_set, union_reset_set, union_guard_set = split(c,max_bound)
    psi_consts = new_abstracted_consts
    c_sat = set()
    c_unsat = set()
    init_sigma = gen_sigma(init_set, "initCondition")
    inverse_sigma = inverse_dict(init_sigma)
    for i in range(max_bound + 1):
        sigma_guard = gen_sigma(union_guard_set[i], "sigmaGuard_" + str(i))
        sigma_reset = gen_sigma(union_reset_set[i], "sigmaReset_" + str(i))
        sigma_tau = gen_sigma(union_tau_set[i], "sigmaTau_" + str(i))
        if i == max_bound:
            sigma_tau.update(gen_sigma(union_tau_set[i + 1], "sigmaTau_" + str(i + 1)))
        new_sigma = dict()
        new_sigma.update(sigma_guard)
        new_sigma.update(sigma_reset)
        new_sigma.update(sigma_tau)
        inverse_sigma.update(inverse_dict(new_sigma))
        psi_consts = substitution(psi_consts, inverse_sigma)
        inverse_sigma.update(inverse_dict(new_sigma))
        for key in inverse_sigma:
            if assignment.eval(key):
                c_sat.add(inverse_sigma[key])
            else:
                c_unsat.add(Not(inverse_sigma[key]))

    for var in alpha:
        if ("newIntegral" in var.id or "newForall" in var.id) and alpha[var] == BoolVal("True"):
            c_sat.add(var)
        elif ("newIntegral" in var.id or "newForall" in var.id) and alpha[var] == BoolVal("False"):
            c_unsat.add(Not(var))

    c_total = c_sat.union(c_unsat)
    new_solver = Z3Solver()
    s_prime = new_solver.unsat_core(Not(psi_consts), list(c_total))
    print(s_prime)
    # s_f_prime = set()
    # original_sigma = inverse_dict(inverse_sigma)
    # for c in z3_bool_to_const_bool(s_prime):
    #     if not (c in original_sigma):
    #         s_f_prime.add(c)
    #     else:
    #         s_f_prime.add(original_sigma[c])

    # revert integral and forall from s_f_prime
    # revert_s_f_prime = set()
    # for c in s_f_prime:
    #     if c in mapping_info





    # gen_hylaa_ha(s_f_prime, max_bound, original_sigma)





    return False, 0, None


@singledispatch
def get_string(const: set):
    var_id_list = list()
    for e in const:
        start_index = int(e.end_vector.id.find("_"))
        var_id = e.end_vector.id[:start_index]
        var_id_list.append(var_id)
    return var_id_list



def gen_hylaa_ha(s_f_prime, max_bound, sigma):
    union_forall_set, union_integral_set, init_set, union_tau_set, union_reset_set, union_guard_set = split(s_f_prime,
                                                                                                            max_bound)
    print(union_integral_set)
    print(get_string(union_integral_set[0]))
    # ha = HybridAutomaton('habrid_automata')
    # for i in range(max_bound + 1):
    #     ha.new_mode("mode"+str(i))


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


def split(S: set, bound: int):
    union_forall_set = list()
    union_integral_set = list()
    union_tau_set = list()
    union_guard_set = list()
    union_reset_set = list()
    init_set = set()
    for i in range(bound + 1):
        forall_set_i = set()
        union_forall_set.append(forall_set_i)

        integral_set_i = set()
        union_integral_set.append(integral_set_i)

        tau_set_i = set()
        union_tau_set.append(tau_set_i)

        guard_set_i = set()
        union_guard_set.append(guard_set_i)

        reset_set_i = set()
        union_reset_set.append(reset_set_i)

    tau_set_end = set()
    union_tau_set.append(tau_set_end)

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
                union_forall_set[bound].add(c)
                S_diff.add(c)
                break

    S = S.difference(S_diff)
    S_diff = set()

    for c in S:
        var_set = get_vars(c)
        for var in var_set:
            start_index = int(var.id.find("#"))
            bound_index = int(var.id.rfind("_"))
            if var.id[:start_index] == "newIntegral":
                bound = int(var.id[bound_index + 1:])
                union_integral_set[bound].add(c)
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
        if max_bound != -1:
            union_tau_set[max_bound].add(c)
            S_diff.add(c)

    S = S.difference(S_diff)
    S_diff = set()

    for c in S:
        if isinstance(c, Eq):
            if isinstance(c.left, Variable):
                start_index = int(c.left.id.find("_"))
                end_index = int(c.left.id.rfind("_"))
                bound = int(c.left.id[start_index + 1:end_index])
                if c.left.id[end_index + 1:] == "0":
                    union_reset_set[bound - 1].add(c)
                    S_diff.add(c)

    S = S.difference(S_diff)
    S_diff = set()

    for c in S:
        var_set = get_vars(c)
        for var in var_set:
            start_index = int(var.id.find("_"))
            end_index = int(var.id.rfind("_"))
            bound = int(var.id[start_index + 1:end_index])
            union_guard_set[bound].add(c)
            S_diff.add(c)
            break
    return union_forall_set, union_integral_set, init_set, union_tau_set, union_reset_set, union_guard_set


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


class HylaaSolver(BaseSolver):
    def __init__(self):
        self._hylaa_model = None

    def solve(self, all_consts, info_dict=None):
        if info_dict is None:
            info_dict = dict()
        result, size, self._hylaa_model = hylaaCheckSat(all_consts, info_dict)
        return result, size

    def make_assignment(self):
        return HylaaAssignment(self._hylaa_model)


class HylaaAssignment(Assignment):
    def __init__(self, p):
        pass

    def get_assignments(self):
        pass


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


# TODO : Should cover Yices and Z3 without notice
def make_c_sat_with_z3(z3_solver_model, clause_list: list):
    return [x for x in clause_list if z3_solver_model.eval(z3Obj(x, True))]


def make_c_unsat_with_z3(z3_solver_model, clause_list: list):
    return [Not(x) for x in clause_list if not z3_solver_model.eval(z3Obj(x, True))]

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
