from functools import singledispatch

from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_integrals_and_foralls, inverse_dict, \
    forall_integral_substitution, substitution, reduce_not
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.abstract_solver import BaseSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.z3 import Z3Solver


def hylaaCheckSat(all_consts, info_dict):
    # pre-processing
    mode_dict, else_dict = divide_dict(info_dict)

    # 1. Build \varphi_ABS and mapping_info
    integral_forall_set = get_integrals_and_foralls(all_consts)
    inverse_mapping_info = gen_fresh_new_var_map(integral_forall_set)
    abstracted_consts = forall_integral_substitution(all_consts, inverse_mapping_info)
    mapping_info = inverse_dict(inverse_mapping_info)

    # 2. Perform process #2 from note
    solver = Z3Solver()
    result, size = solver.solve(abstracted_consts)

    if result:
        return True, 0, None
    assignment = solver.make_assignment()
    alpha = assignment.get_assignments()
    new_alpha = gen_net_assignment(alpha, info_dict)
    new_abstracted_consts = substitution(abstracted_consts, new_alpha)
    c = clause(new_abstracted_consts)
    c_sat = set()
    c_unsat = set()
    for c_elem in c:
        if assignment.eval(c_elem):
            c_sat.add(c_elem)
        else:
            c_unsat.add(reduce_not(Not(c_elem)))
    s = c_sat.union(c_unsat)
    return False, 0, None


def gen_net_assignment(mapping: dict, range_dict: dict):
    new_dict = dict()
    for var in mapping:
        search_index = var.id.find("_")
        search_id = var.id[:search_index]
        if not (Real(search_id) in range_dict or "tau" in var.id):
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
    new_id = "newIntegral_" + str(const.current_mode_number) + "_" + bound_str
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
