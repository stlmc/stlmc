from functools import singledispatch

from .constraints import (
    Add, And, Bool, Eq, Forall, Function, Geq, Gt, Mul, Neq, Ode, Or, Real,
    RealVal, Sub, Neg,
)
from .analysis import get_vars
from .differentiation import diff, differentiate_polynomial
from .substitution import substitution
from .normalization import substitution_zero2t


def make_forall_consts_aux(forall: Forall):
    start_forall_exp = forall.const.left
    end_forall_exp = substitution_zero2t(forall.const.left)
    mn = forall.current_mode_number
    end = forall.end_tau
    start = forall.start_tau
    integral = forall.integral
    zero = RealVal("0")
    derivative = diff(start_forall_exp, integral)
    non_decreasing = Forall(
        mn, end, start, Geq(derivative, zero), integral
    )
    non_increasing = Forall(
        mn, end, start, Geq(zero - derivative, zero), integral
    )

    if isinstance(forall.const, Geq):
        return Or([
            And([non_decreasing, Geq(start_forall_exp, zero)]),
            And([non_increasing, Geq(end_forall_exp, zero)]),
        ])

    # Lemma 6.2(2): on an open interval a strict invariant may be zero at
    # the excluded endpoint when it is strictly positive at the other end.
    increasing_endpoint = Or([
        Gt(start_forall_exp, zero),
        And([Eq(start_forall_exp, zero), Gt(end_forall_exp, zero)]),
    ])
    decreasing_endpoint = Or([
        Gt(end_forall_exp, zero),
        And([Eq(end_forall_exp, zero), Gt(start_forall_exp, zero)]),
    ])
    return Or([
        And([non_decreasing, increasing_endpoint]),
        And([non_increasing, decreasing_endpoint]),
    ])


def make_forall_consts(forall: Forall):
    if isinstance(forall.const, Bool) or len(get_vars(forall.const)) == 0:
        return forall.const
    if isinstance(forall.integral.dynamics, Function):
        return _make_solution_forall_consts(forall)
    if isinstance(forall.const, Eq):
        return And([forall.const, substitution_zero2t(forall.const),
                    Forall(forall.current_mode_number,
                           forall.end_tau, forall.start_tau,
                           Eq(diff(forall.const.left, forall.integral), RealVal('0')),
                           forall.integral)])
    elif isinstance(forall.const, Neq):
        first_const = make_forall_consts(Forall(forall.current_mode_number,
                                                forall.end_tau, forall.start_tau,
                                                Gt(forall.const.left, RealVal('0')),
                                                forall.integral))
        second_const = make_forall_consts(Forall(forall.current_mode_number,
                                                 forall.end_tau, forall.start_tau,
                                                 Gt(RealVal('0'), forall.const.left),
                                                 forall.integral))
        return Or([first_const, second_const])
    else:
        return make_forall_consts_aux(forall)


def _make_solution_forall_consts(forall):
    """Apply Lemma 6.2 to a polynomial in local elapsed time, once expanded.

    Derivatives must never be re-instantiated through the flow: its initial
    state symbols remain constant parameters at every derivative order.
    """
    from .quantified_flow import flow_condition_at_time

    variables = get_vars(forall.const)
    for expression in forall.integral.dynamics.exps:
        variables |= get_vars(expression)
    name = "__stlmc_polynomial_elapsed"
    while Real(name) in variables:
        name += "_"
    elapsed = Real(name)
    condition = flow_condition_at_time(forall, elapsed)
    duration = Sub(forall.end_tau, forall.start_tau)
    zero = RealVal("0")

    def eliminate(expression, operator):
        start = substitution(expression, {elapsed: zero})
        end = substitution(expression, {elapsed: duration})
        if elapsed not in get_vars(expression):
            return operator(expression, zero)
        derivative = differentiate_polynomial(expression, elapsed)
        if operator is Eq:
            return And([Eq(start, zero), eliminate(derivative, Eq)])
        if operator is Neq:
            return Or([eliminate(expression, Gt), eliminate(Neg(expression), Gt)])
        increasing = eliminate(derivative, Geq)
        decreasing = eliminate(Neg(derivative), Geq)
        if operator is Geq:
            return Or([And([increasing, Geq(start, zero)]),
                       And([decreasing, Geq(end, zero)])])
        return Or([
            And([increasing, Or([Gt(start, zero),
                                  And([Eq(start, zero), Gt(end, zero)])])]),
            And([decreasing, Or([Gt(end, zero),
                                  And([Eq(end, zero), Gt(start, zero)])])]),
        ])

    return eliminate(Sub(condition.left, condition.right), type(condition))


@singledispatch
def make_dynamics_consts(dyn: Ode):
    dyn_const_children = list()
    index = 0
    for exp in dyn.exps:
        var = dyn.vars[index]
        start_index = var.id[0:-2].find("_") + 1
        bound_str = var.id[start_index:-4]

        old_var_id = var.id[0: start_index - 1]
        new_end_var_id = old_var_id + "_" + bound_str + "_t"
        new_start_var_id = old_var_id + "_" + bound_str + "_0"

        new_end_var = Real(new_end_var_id)
        new_start_var = Real(new_start_var_id)

        end_tau_var = Real('tau_' + str(int(bound_str) + 1))
        if bound_str == "0":
            start_tau_var = RealVal("0")
        else:
            start_tau_var = Real('tau_' + bound_str)

        new_exp_const = Eq(new_end_var, Add(new_start_var, Mul(Sub(end_tau_var, start_tau_var), exp)))
        dyn_const_children.append(new_exp_const)
        index += 1
    return And(dyn_const_children)


@make_dynamics_consts.register(Function)
def _(dyn: Function):
    dyn_const_children = list()
    index = 0
    for exp in dyn.exps:
        var = dyn.vars[index]
        start_index = var.id[0:-2].find("_") + 1
        bound_str = var.id[start_index:-4]

        old_var_id = var.id[0: start_index - 1]
        new_end_var_id = old_var_id + "_" + bound_str + "_t"

        new_end_var = Real(new_end_var_id)
        new_exp_const = Eq(new_end_var, exp)
        dyn_const_children.append(new_exp_const)
        index += 1

    return And(dyn_const_children)
