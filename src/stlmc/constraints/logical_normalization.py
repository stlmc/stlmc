"""Negation reduction for Boolean and temporal formulae."""

from functools import singledispatch

from ..exceptions import NotSupportedError
from .constraints import (
    And, Bool, BoolVal, Constant, Constraint, Eq, FinallyFormula, Geq,
    GloballyFormula, Gt, Implies, Leq, Lt, Neq, Not, Or, ReleaseFormula,
    UntilFormula,
)


@singledispatch
def reduce_not(const: Constraint):
    return const


@reduce_not.register(Not)
def _(const: Not):
    child = const.child
    if isinstance(child, Lt):
        return Geq(child.left, child.right)
    if isinstance(child, Gt):
        return Leq(child.left, child.right)
    if isinstance(child, Leq):
        return Gt(child.left, child.right)
    if isinstance(child, Geq):
        return Lt(child.left, child.right)
    if isinstance(child, Eq):
        return Neq(child.left, child.right)
    if isinstance(child, Neq):
        return Eq(child.left, child.right)
    if isinstance(child, Constant):
        if child.value == "True":
            return BoolVal("False")
        if child.value == "False":
            return BoolVal("True")
        raise NotSupportedError("real or integer constants cannot be negated")
    if isinstance(child, And):
        return Or([reduce_not(Not(item)) for item in child.children])
    if isinstance(child, Or):
        return And([reduce_not(Not(item)) for item in child.children])
    if isinstance(child, Implies):
        return And([reduce_not(child.left), reduce_not(Not(child.right))])
    if isinstance(child, FinallyFormula):
        return GloballyFormula(
            child.local_time, child.global_time, reduce_not(Not(child.child)),
        )
    if isinstance(child, GloballyFormula):
        return FinallyFormula(
            child.local_time, child.global_time, reduce_not(Not(child.child)),
        )
    if isinstance(child, UntilFormula):
        return ReleaseFormula(
            child.local_time, child.global_time,
            reduce_not(Not(child.left)), reduce_not(Not(child.right)),
        )
    if isinstance(child, ReleaseFormula):
        return UntilFormula(
            child.local_time, child.global_time,
            reduce_not(Not(child.left)), reduce_not(Not(child.right)),
        )
    if isinstance(child, Not):
        return child.child
    if isinstance(child, Bool):
        return Bool("not@" + child.id)
    return const


@reduce_not.register(And)
def _(const: And):
    return And([reduce_not(child) for child in const.children])


@reduce_not.register(Or)
def _(const: Or):
    return Or([reduce_not(child) for child in const.children])


@reduce_not.register(Implies)
def _(const: Implies):
    return Implies(reduce_not(const.left), reduce_not(const.right))


@reduce_not.register(Eq)
def _(const: Eq):
    return Eq(reduce_not(const.left), reduce_not(const.right))


@reduce_not.register(Neq)
def _(const: Neq):
    return Neq(reduce_not(const.left), reduce_not(const.right))


def _reduce_unary_temporal(const):
    return type(const)(
        const.local_time, const.global_time, reduce_not(const.child),
    )


reduce_not.register(FinallyFormula)(_reduce_unary_temporal)
reduce_not.register(GloballyFormula)(_reduce_unary_temporal)


def _reduce_binary_temporal(const):
    return type(const)(
        const.local_time, const.global_time,
        reduce_not(const.left), reduce_not(const.right),
    )


reduce_not.register(UntilFormula)(_reduce_binary_temporal)
reduce_not.register(ReleaseFormula)(_reduce_binary_temporal)
