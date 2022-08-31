from typing import Dict

from ....constraints.aux.generator import *
from ....constraints.constraints import *


# add bound to variables
def indexed_var_0(var: Variable, bound: int):
    return variable("{}^0@{}".format(var.id, bound), var.type)


# add bound to variables
def indexed_var_t(var: Variable, bound: int):
    return variable("{}^t@{}".format(var.id, bound), var.type)


def non_indexed_var(var: Variable):
    # get name of indexed variable
    v_id = var.id.split("^")[0]
    return variable(v_id, var.type)


def indexed_mode_var(var: Variable, bound: int):
    return variable("{}@{}".format(var.id, bound), var.type)


# next variables
def next_mode_var(var: Variable, bound: int):
    return variable("{}@{}".format(var.id, bound + 1), var.type)


def next_continuous_var(var: Variable, bound: int):
    return indexed_var_0(var, bound + 1)


def tau(bound: int):
    return Real("tau_{}".format(bound))


def is_track_var(track_v: Variable, abs_keyword: str, bound: int):
    is_bool_type = track_v.type == "bool"

    # bool type & @{ bound } \in id & v_name \in id
    if "@{}".format(bound) in track_v.id and is_bool_type and abs_keyword in track_v.id:
        return True
    else:
        return False


def range_consts(var: Real, bound: int, range_info: Dict[Real, Interval]):
    def interval2const(_v: Real, _i: Interval):
        interval_type = {True: Leq, False: Lt}
        left = interval_type[_i.left_end](_i.left, _v)
        right = interval_type[_i.right_end](_v, _i.right)
        return left, right

    if var.type != "real" or var not in range_info:
        raise Exception("{} type variable is not a continuous variable")

    v_0, v_t = indexed_var_0(var, bound), indexed_var_t(var, bound)
    v_range = range_info[var]

    s_l, s_r = interval2const(v_0, v_range)
    e_l, e_r = interval2const(v_t, v_range)

    # do not add constraint when infinity
    m_inf = RealVal("-inf")
    p_inf = RealVal("inf")

    range_const = list()
    if v_range.left != m_inf:
        range_const.extend([s_l, s_r])

    if v_range.right != p_inf:
        range_const.extend([e_l, e_r])

    return range_const


def flat_jump(jump_pre: Formula, jump_post: Formula):
    return And([jump_pre, jump_post])


# @singledispatch
# def make_new_dynamics(dyn: Ode, bound, mode_var_dict, range_dict, constant_dict):
#     new_dynamics_dict = make_dict(bound, mode_var_dict, range_dict, constant_dict, "_0")
#     new_dynamics_dict[Real('time')] = Real('tau_' + str(bound + 1))
#     new_exps = list()
#     for exp in dyn.exps:
#         new_exp = substitution(exp, new_dynamics_dict)
#         new_exps.append(new_exp)
#
#     new_vars_dict = make_dict(bound, {}, range_dict, {}, "_0_t")
#     new_vars = list()
#     for var in dyn.vars:
#         new_var = substitution(var, new_vars_dict)
#         new_vars.append(new_var)
#     return Ode(new_vars, new_exps)
#
#
# @make_new_dynamics.register(Function)
# def _(dyn: Function, bound, mode_var_dict, range_dict, constant_dict):
#     new_dynamics_dict = make_dict(bound, mode_var_dict, range_dict, constant_dict, "_0")
#     new_dynamics_dict[Real('time')] = Real('tau_' + str(bound + 1))
#     new_exps = list()
#     for exp in dyn.exps:
#         new_exp = substitution(exp, new_dynamics_dict)
#         new_exps.append(new_exp)
#
#     new_vars_dict = make_dict(bound, {}, range_dict, {}, "_0_t")
#     new_vars = list()
#     for var in dyn.vars:
#         new_var = substitution(var, new_vars_dict)
#         new_vars.append(new_var)
#     return Function(new_vars, new_exps)
