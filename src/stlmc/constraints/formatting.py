"""Text formatting helpers for constraint expressions."""

from functools import singledispatch

from .constraints import (
    Add, And, Constraint, Div, Eq, Forall, Geq, Gt, Leq, Lt, Mul, Neg, Neq,
    Pow, Sub, Variable,
)


@singledispatch
def infix(const: Constraint):
    return str(const)


@infix.register(Variable)
def _(const: Variable):
    return const.id


@infix.register(And)
def _(const: And):
    return '&'.join([infix(c) for c in const.children])


@infix.register(Geq)
def _(const: Geq):
    return infix(const.left) + " >= " + infix(const.right)


@infix.register(Gt)
def _(const: Gt):
    return infix(const.left) + " > " + infix(const.right)


@infix.register(Leq)
def _(const: Leq):
    return infix(const.left) + " <= " + infix(const.right)


@infix.register(Lt)
def _(const: Lt):
    return infix(const.left) + " < " + infix(const.right)


@infix.register(Eq)
def _(const: Eq):
    return infix(const.left) + " == " + infix(const.right)


@infix.register(Neq)
def _(const: Neq):
    return infix(const.left) + " != " + infix(const.right)


@infix.register(Add)
def _(const: Add):
    return "(" + infix(const.left) + " + " + infix(const.right) + ")"


@infix.register(Sub)
def _(const: Sub):
    return "(" + infix(const.left) + " - " + infix(const.right) + ")"


@infix.register(Neg)
def _(const: Neg):
    return "(-" + infix(const.child) + ")"


@infix.register(Mul)
def _(const: Mul):
    return "(" + infix(const.left) + " * " + infix(const.right) + ")"


@infix.register(Div)
def _(const: Div):
    return "(" + infix(const.left) + " / " + infix(const.right) + ")"


@infix.register(Pow)
def _(const: Pow):
    return "(" + infix(const.left) + " ** " + infix(const.right) + ")"


@infix.register(Forall)
def _(const: Forall):
    return infix(const.const)
