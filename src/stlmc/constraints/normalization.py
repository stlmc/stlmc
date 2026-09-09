"""Local normalization operations over constraint trees."""

from functools import singledispatch

from .constraints import (
    Add, And, Binary, BinaryTemporalFormula, Bool, Constraint, Div, Eq, Geq,
    Gt, Implies, Int, Leq, Lt, Mul, Neg, Neq, Not, Or, Pow, Real, Sub,
    TimeBoundConst, UnaryTemporalFormula, Variable,
)


@singledispatch
def reverse_inequality(const: Constraint):
    return const


@reverse_inequality.register(Lt)
def _(const: Lt):
    return Gt(Neg(const.left), Neg(const.right))


@reverse_inequality.register(Leq)
def _(const: Leq):
    return Geq(Neg(const.left), Neg(const.right))


@singledispatch
def substitution_zero2t(const: Constraint):
    return const


@substitution_zero2t.register(Neg)
def _(const: Neg):
    return Neg(substitution_zero2t(const.child))


@substitution_zero2t.register(Not)
def _(const: Not):
    return Not(substitution_zero2t(const.child))


@substitution_zero2t.register(Binary)
def _(const: Binary):
    operator = {
        Geq: Geq, Gt: Gt, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq,
        Add: Add, Sub: Sub, Div: Div, Mul: Mul, Pow: Pow,
        Implies: Implies, TimeBoundConst: TimeBoundConst,
    }[type(const)]
    return operator(
        substitution_zero2t(const.left),
        substitution_zero2t(const.right),
    )


@substitution_zero2t.register(UnaryTemporalFormula)
def _(const: UnaryTemporalFormula):
    return type(const)(
        const.local_time, const.global_time,
        substitution_zero2t(const.child),
    )


@substitution_zero2t.register(BinaryTemporalFormula)
def _(const: BinaryTemporalFormula):
    return type(const)(
        const.local_time, const.global_time,
        substitution_zero2t(const.left),
        substitution_zero2t(const.right),
    )


@substitution_zero2t.register(And)
def _(const: And):
    return And([substitution_zero2t(c) for c in const.children])


@substitution_zero2t.register(Or)
def _(const: Or):
    return Or([substitution_zero2t(c) for c in const.children])


@substitution_zero2t.register(Variable)
def _(const: Variable):
    variable_type = Bool if isinstance(const, Bool) else (
        Int if isinstance(const, Int) else Real
    )
    if const.id.find("_") != const.id.rfind("_") and const.id.endswith("_0"):
        return variable_type(const.id[:-2] + "_t")
    return const
