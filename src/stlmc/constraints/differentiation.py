"""Symbolic differentiation for expressions along an integral flow."""

from functools import singledispatch
from fractions import Fraction

from ..exceptions import NotSupportedError
from .analysis import get_vars
from .constraints import (
    Add, Constant, Constraint, Div, Expr, Function, Integral, Mul, Neg, Ode,
    Pow, Real, RealVal, Sub, Variable,
)
from .substitution import substitution


def diff(exp: Expr, integral: Integral):
    new_exp = substitution(exp, make_diff_mapping(integral))
    if isinstance(integral.dynamics, Function):
        # Closed-form flows use local elapsed time (tau_end - tau_start).
        # Differentiate with respect to tau_end while holding tau_start fixed.
        end_id = integral.end_vector[0].id
        bound = end_id[end_id.find("_") + 1:end_id.rfind("_")]
        new_exp = substitution(new_exp, {Real("tau_" + bound): RealVal("0")})
    if not supports_symbolic_differentiation(new_exp):
        raise NotSupportedError(
            "cannot apply polynomial invariant simplification to {}"
            .format(new_exp)
        )
    return diff_aux(new_exp)


def supports_symbolic_differentiation(const: Constraint) -> bool:
    """Return whether ``diff_aux`` can soundly differentiate ``const``."""
    if isinstance(const, (Constant, Variable)):
        return True
    if isinstance(const, Neg):
        return supports_symbolic_differentiation(const.child)
    if isinstance(const, (Add, Sub, Mul, Div)):
        return (
            supports_symbolic_differentiation(const.left)
            and supports_symbolic_differentiation(const.right)
        )
    if isinstance(const, Pow):
        if not isinstance(const.left, Variable) or get_vars(const.right):
            return False
        try:
            _constant_value(const.right)
        except (NotSupportedError, ValueError, ZeroDivisionError):
            return False
        return True
    return False


def make_diff_mapping(integral: Integral):
    result = {}
    for index, dyn_var in enumerate(integral.start_vector):
        if not isinstance(integral.dynamics, Ode):
            result[dyn_var] = integral.dynamics.exps[index]
            continue

        end_id = integral.end_vector[0].id
        bound = end_id[end_id.find("_") + 1:end_id.rfind("_")]
        end_tau = Real("tau_" + str(int(bound) + 1))
        result[dyn_var] = Mul(integral.dynamics.exps[index], end_tau)
    return result


@singledispatch
def diff_aux(const: Constraint):
    raise NotSupportedError(
        "unsupported expression for symbolic differentiation: {}"
        .format(type(const).__name__)
    )


@diff_aux.register(Constant)
def _(const: Constant):
    return RealVal("0")


@diff_aux.register(Variable)
def _(const: Variable):
    return RealVal("1" if str(const.id).startswith("tau") else "0")


@diff_aux.register(Add)
def _(const: Add):
    x, y = const.left, const.right
    if not get_vars(const):
        return RealVal("0")
    if not get_vars(x):
        return diff_aux(y)
    if not get_vars(y):
        return diff_aux(x)
    return Add(diff_aux(x), diff_aux(y))


@diff_aux.register(Sub)
def _(const: Sub):
    x, y = const.left, const.right
    if not get_vars(const):
        return RealVal("0")
    if not get_vars(x):
        return Neg(diff_aux(y))
    if not get_vars(y):
        return diff_aux(x)
    return Sub(diff_aux(x), diff_aux(y))


@diff_aux.register(Pow)
def _(const: Pow):
    x, y = const.left, const.right
    if not isinstance(x, Variable) or len(get_vars(y)) != 0:
        raise NotSupportedError(
            "Cannot handling polynomial yet : {}".format(const)
        )
    if _constant_value(y) == 0:
        return RealVal("0")
    if str(x.id).startswith("tau"):
        return Mul(y, Pow(x, Sub(y, RealVal("1"))))
    return RealVal("0")


def _constant_value(const):
    if isinstance(const, Constant):
        return Fraction(const.value)
    if isinstance(const, Neg):
        return -_constant_value(const.child)
    if isinstance(const, Add):
        return _constant_value(const.left) + _constant_value(const.right)
    if isinstance(const, Sub):
        return _constant_value(const.left) - _constant_value(const.right)
    if isinstance(const, Mul):
        return _constant_value(const.left) * _constant_value(const.right)
    if isinstance(const, Div):
        return _constant_value(const.left) / _constant_value(const.right)
    if isinstance(const, Pow):
        exponent = _constant_value(const.right)
        if exponent.denominator != 1:
            raise NotSupportedError("fractional constant exponents are unsupported")
        return _constant_value(const.left) ** exponent.numerator
    raise NotSupportedError("expected a constant arithmetic expression")


@diff_aux.register(Mul)
def _(const: Mul):
    x, y = const.left, const.right
    if len(get_vars(const)) == 0:
        return RealVal("0")
    if len(get_vars(x)) == 0:
        return Mul(x, diff_aux(y))
    if len(get_vars(y)) == 0:
        return Mul(diff_aux(x), y)
    return Add(Mul(diff_aux(x), y), Mul(x, diff_aux(y)))


@diff_aux.register(Div)
def _(const: Div):
    x, y = const.left, const.right
    if len(get_vars(const)) == 0:
        return RealVal("0")
    if len(get_vars(x)) == 0:
        return Sub(RealVal("0"), Div(Mul(diff_aux(y), x), Mul(y, y)))
    if len(get_vars(y)) == 0:
        return Div(diff_aux(x), y)
    return Sub(Div(diff_aux(x), y), Div(Mul(diff_aux(y), x), Mul(y, y)))


@diff_aux.register(Neg)
def _(const: Neg):
    return Neg(diff_aux(const.child))
