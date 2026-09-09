"""Transform temporal formulae to a finite global time bound."""

from functools import singledispatch

from .constraints import (
    And, Constraint, Eq, FinallyFormula, GloballyFormula, Implies, Interval,
    Neq, Or, RealVal, ReleaseFormula, UntilFormula,
)


@singledispatch
def bound_tau_max(const: Constraint, time_bound):
    return const


@bound_tau_max.register(And)
def _(const: And, time_bound):
    return And([bound_tau_max(child, time_bound) for child in const.children])


@bound_tau_max.register(Or)
def _(const: Or, time_bound):
    return Or([bound_tau_max(child, time_bound) for child in const.children])


def _bound_binary(const, time_bound):
    return type(const)(
        bound_tau_max(const.left, time_bound),
        bound_tau_max(const.right, time_bound),
    )


bound_tau_max.register(Implies)(_bound_binary)
bound_tau_max.register(Eq)(_bound_binary)
bound_tau_max.register(Neq)(_bound_binary)


def _bounded_interval(const, time_bound):
    global_time = const.global_time
    return Interval(
        global_time.left_end, global_time.left, True, RealVal(str(time_bound)),
    )


@bound_tau_max.register(FinallyFormula)
def _(const: FinallyFormula, time_bound):
    return FinallyFormula(
        const.local_time, _bounded_interval(const, time_bound),
        bound_tau_max(const.child, time_bound),
    )


@bound_tau_max.register(GloballyFormula)
def _(const: GloballyFormula, time_bound):
    return GloballyFormula(
        const.local_time, _bounded_interval(const, time_bound),
        bound_tau_max(const.child, time_bound),
    )


@bound_tau_max.register(UntilFormula)
def _(const: UntilFormula, time_bound):
    return UntilFormula(
        const.local_time, _bounded_interval(const, time_bound),
        bound_tau_max(const.left, time_bound),
        bound_tau_max(const.right, time_bound),
    )


@bound_tau_max.register(ReleaseFormula)
def _(const: ReleaseFormula, time_bound):
    bounded_interval = _bounded_interval(const, time_bound)
    bounded_left = bound_tau_max(const.left, time_bound)
    return And([
        ReleaseFormula(
            const.local_time, bounded_interval, bounded_left,
            bound_tau_max(const.right, time_bound),
        ),
        FinallyFormula(
            Interval(True, RealVal("0"), False, RealVal("inf")),
            bounded_interval, bounded_left,
        ),
    ])
