"""Numeric evaluation of STLmc arithmetic expression trees."""

from functools import singledispatch

import numpy as np

from ..constraints.constraints import (
    Add, Arccos, Arcsin, Arctan, Constraint, Cos, Div, Int, IntVal, Mul,
    Neg, Pow, Real, RealVal, Sin, Sqrt, Sub, Tan,
)
from ..exceptions import NotSupportedError
from .numbers import number_float, parse_number


@singledispatch
def infix_float(constraint: Constraint, values, variables: list):
    raise NotSupportedError("cannot convert this: {}".format(constraint))


@infix_float.register(Neg)
def _(constraint: Neg, values, variables: list):
    return -infix_float(constraint.child, values, variables)


@infix_float.register(IntVal)
def _(constraint: IntVal, values, variables: list):
    value = parse_number(constraint.value)
    if not hasattr(value, "denominator") or value.denominator != 1:
        raise ValueError("integer constant must be a finite integer")
    # Sampling uses floating-point arithmetic: do not create unbounded Python
    # integers when a typed Pow combines large integer constants.
    return number_float(value)


@infix_float.register(RealVal)
def _(constraint: RealVal, values, variables: list):
    return number_float(constraint.value)


@infix_float.register(Int)
@infix_float.register(Real)
def _(constraint, values, variables: list):
    return values[variables.index(constraint)]


def _binary(constraint, values, variables, operation):
    return operation(
        infix_float(constraint.left, values, variables),
        infix_float(constraint.right, values, variables),
    )


@infix_float.register(Add)
def _(constraint: Add, values, variables: list):
    return _binary(constraint, values, variables, lambda left, right: left + right)


@infix_float.register(Sub)
def _(constraint: Sub, values, variables: list):
    return _binary(constraint, values, variables, lambda left, right: left - right)


@infix_float.register(Mul)
def _(constraint: Mul, values, variables: list):
    return _binary(constraint, values, variables, lambda left, right: left * right)


@infix_float.register(Div)
def _(constraint: Div, values, variables: list):
    return _binary(constraint, values, variables, lambda left, right: left / right)


@infix_float.register(Pow)
def _(constraint: Pow, values, variables: list):
    return _binary(constraint, values, variables, lambda left, right: left ** right)


@infix_float.register(Sqrt)
def _(constraint: Sqrt, values, variables: list):
    return np.sqrt(infix_float(constraint.child, values, variables))


@infix_float.register(Sin)
def _(constraint: Sin, values, variables: list):
    return np.sin(infix_float(constraint.child, values, variables))


@infix_float.register(Cos)
def _(constraint: Cos, values, variables: list):
    return np.cos(infix_float(constraint.child, values, variables))


@infix_float.register(Tan)
def _(constraint: Tan, values, variables: list):
    return np.tan(infix_float(constraint.child, values, variables))


@infix_float.register(Arcsin)
def _(constraint: Arcsin, values, variables: list):
    return np.arcsin(infix_float(constraint.child, values, variables))


@infix_float.register(Arccos)
def _(constraint: Arccos, values, variables: list):
    return np.arccos(infix_float(constraint.child, values, variables))


@infix_float.register(Arctan)
def _(constraint: Arctan, values, variables: list):
    return np.arctan(infix_float(constraint.child, values, variables))


__all__ = ["infix_float"]
