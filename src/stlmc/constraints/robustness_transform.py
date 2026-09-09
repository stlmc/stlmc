"""Epsilon weakening and strengthening of STL formulae."""

from functools import singledispatch

from .constraints import (
    Add, And, BinaryTemporalFormula, Bool, Eq, Formula, Geq, Gt, Implies,
    Leq, Lt, Neq, Not, Or, RealVal, Sub, UnaryTemporalFormula,
)


@singledispatch
def relaxing(const: Formula, delta: float):
    """Return the epsilon-weakening of ``const``."""
    return const


@singledispatch
def strengthening(const: Formula, delta: float):
    """Return the epsilon-strengthening of ``const``."""
    return const


@relaxing.register(And)
def _(const: And, delta: float):
    return And([relaxing(child, delta) for child in const.children])


@relaxing.register(Or)
def _(const: Or, delta: float):
    return Or([relaxing(child, delta) for child in const.children])


@relaxing.register(Not)
def _(const: Not, delta: float):
    return Not(strengthening(const.child, delta))


@strengthening.register(Not)
def _(const: Not, delta: float):
    return Not(relaxing(const.child, delta))


@relaxing.register(Implies)
def _(const: Implies, delta: float):
    return Implies(strengthening(const.left, delta), relaxing(const.right, delta))


@strengthening.register(Implies)
def _(const: Implies, delta: float):
    return Implies(relaxing(const.left, delta), strengthening(const.right, delta))


@relaxing.register(Geq)
def _(const: Geq, delta: float):
    return Geq(const.left, Sub(const.right, RealVal(str(delta))))


@relaxing.register(Gt)
def _(const: Gt, delta: float):
    return Gt(const.left, Sub(const.right, RealVal(str(delta))))


@relaxing.register(Leq)
def _(const: Leq, delta: float):
    return Leq(const.left, Add(const.right, RealVal(str(delta))))


@relaxing.register(Lt)
def _(const: Lt, delta: float):
    return Lt(const.left, Add(const.right, RealVal(str(delta))))


@relaxing.register(Eq)
def _(const: Eq, delta: float):
    if isinstance(const.left, Bool) or isinstance(const.right, Bool):
        return const
    epsilon = RealVal(str(delta))
    return And([
        Geq(const.left, Sub(const.right, epsilon)),
        Leq(const.left, Add(const.right, epsilon)),
    ])


@relaxing.register(Neq)
def _(const: Neq, delta: float):
    if isinstance(const.left, Bool) or isinstance(const.right, Bool):
        return const
    epsilon = RealVal(str(delta))
    return Or([
        Lt(const.left, Add(const.right, epsilon)),
        Gt(const.left, Sub(const.right, epsilon)),
    ])


@relaxing.register(BinaryTemporalFormula)
def _(const: BinaryTemporalFormula, delta: float):
    return type(const)(
        const.local_time, const.global_time,
        relaxing(const.left, delta), relaxing(const.right, delta),
    )


@relaxing.register(UnaryTemporalFormula)
def _(const: UnaryTemporalFormula, delta: float):
    return type(const)(
        const.local_time, const.global_time, relaxing(const.child, delta),
    )


@strengthening.register(And)
def _(const: And, delta: float):
    return And([strengthening(child, delta) for child in const.children])


@strengthening.register(Or)
def _(const: Or, delta: float):
    return Or([strengthening(child, delta) for child in const.children])


@strengthening.register(Geq)
def _(const: Geq, delta: float):
    return Geq(const.left, Add(const.right, RealVal(str(delta))))


@strengthening.register(Gt)
def _(const: Gt, delta: float):
    return Gt(const.left, Add(const.right, RealVal(str(delta))))


@strengthening.register(Leq)
def _(const: Leq, delta: float):
    return Leq(const.left, Sub(const.right, RealVal(str(delta))))


@strengthening.register(Lt)
def _(const: Lt, delta: float):
    return Lt(const.left, Sub(const.right, RealVal(str(delta))))


@strengthening.register(Eq)
def _(const: Eq, delta: float):
    if isinstance(const.left, Bool) or isinstance(const.right, Bool):
        return const
    epsilon = RealVal(str(delta))
    return And([
        Geq(const.left, Add(const.right, epsilon)),
        Leq(const.left, Sub(const.right, epsilon)),
    ])


@strengthening.register(Neq)
def _(const: Neq, delta: float):
    if isinstance(const.left, Bool) or isinstance(const.right, Bool):
        return const
    epsilon = RealVal(str(delta))
    return Or([
        Lt(const.left, Sub(const.right, epsilon)),
        Gt(const.left, Add(const.right, epsilon)),
    ])


@strengthening.register(BinaryTemporalFormula)
def _(const: BinaryTemporalFormula, delta: float):
    return type(const)(
        const.local_time, const.global_time,
        strengthening(const.left, delta), strengthening(const.right, delta),
    )


@strengthening.register(UnaryTemporalFormula)
def _(const: UnaryTemporalFormula, delta: float):
    return type(const)(
        const.local_time, const.global_time, strengthening(const.child, delta),
    )
