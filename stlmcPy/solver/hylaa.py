from functools import singledispatch

from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_integrals_and_foralls, substitution, inverse_dict
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.abstract_solver import BaseSolver
from stlmcPy.solver.assignment import Assignment
from stlmcPy.solver.solver_factory import SolverFactory


def hylaaCheckSat(all_consts, info_dict):
    # pre-processing
    mode_dict, else_dict = divide_dict(info_dict)

    # 1. Build \varphi_ABS and mapping_info
    integral_forall_set = get_integrals_and_foralls(all_consts)
    inverse_mapping_info = gen_fresh_new_var_map(integral_forall_set)
    abstracted_consts = substitution(all_consts, inverse_mapping_info)
    mapping_info = inverse_dict(inverse_mapping_info)

    # 2. Perform process #2 from note
    # solver = SolverFactory("z3").generate_solver()
    # result, size = solver.solve(abstracted_consts)
    # assignment = solver.m






@singledispatch
def gen_fresh_new_var_map_aux(const: Constraint, id_str=None):
    raise NotSupportedError("cannot create mapping for integral and forall")


@gen_fresh_new_var_map_aux.register(Integral)
def _(const: Integral, id_str=None):
    if id_str is None:
        id_str = "newIntegral_"
    new_map = dict()
    end_var_str = const.end_vector[0].id
    start_index = end_var_str.find('_')
    bound_str = end_var_str[start_index:-3]
    new_id = id_str + str(const.current_mode_number) + "_" + bound_str
    new_map[const] = Bool(new_id)
    return new_map


@gen_fresh_new_var_map_aux.register(Forall)
def _(const: Forall):
    return gen_fresh_new_var_map_aux(const.integral, "newForall#"+str(id(const))+"_")


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

    def make_assignment(self, integrals_list, mode_var_dict, cont_var_dict):
        return HylaaAssignment(self._z3_model, integrals_list, mode_var_dict, cont_var_dict)


class HylaaAssignment(Assignment):
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
    return [const]


@clause.register(And)
def _(const: And):
    result = list()
    for c in list(const.children):
        result.extend(clause(c))
    return result


@clause.register(Or)
def _(const: Or):
    result = list()
    for c in list(const.children):
        result.extend(clause(c))
    return result


@clause.register(Not)
def _(const: Not):
    result = list()
    result.extend(clause(const.child))
    return result


@clause.register(Implies)
def _(const):
    result = list()
    result.extend(clause(const.left))
    result.extend(clause(const.right))
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
