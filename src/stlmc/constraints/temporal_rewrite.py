"""Semantics-preserving rewrites for bounded binary STL operators."""

from functools import singledispatch

from .constraints import (
    And, FinallyFormula, Formula, GloballyFormula, Implies, Not, Or,
    RealVal, ReleaseFormula, UntilFormula,
)
from .interval import Interval, universeInterval


@singledispatch
def to_unary_bounded_temporal_form(formula: Formula):
    """Return an equivalent form whose bounded temporal operators are unary.

    The result is equivalent under continuous-time STL semantics, but it has
    more temporal subformulas.  Its fully-stable partition bound therefore is
    not directly comparable with the bound of the unreduced formula.
    """
    return formula


@to_unary_bounded_temporal_form.register(Not)
def _(formula: Not):
    return Not(to_unary_bounded_temporal_form(formula.child))


@to_unary_bounded_temporal_form.register(And)
def _(formula: And):
    return And([
        to_unary_bounded_temporal_form(child) for child in formula.children
    ])


@to_unary_bounded_temporal_form.register(Or)
def _(formula: Or):
    return Or([
        to_unary_bounded_temporal_form(child) for child in formula.children
    ])


@to_unary_bounded_temporal_form.register(Implies)
def _(formula: Implies):
    return Implies(
        to_unary_bounded_temporal_form(formula.left),
        to_unary_bounded_temporal_form(formula.right),
    )


@to_unary_bounded_temporal_form.register(FinallyFormula)
def _(formula: FinallyFormula):
    return FinallyFormula(
        formula.local_time,
        formula.global_time,
        to_unary_bounded_temporal_form(formula.child),
    )


@to_unary_bounded_temporal_form.register(GloballyFormula)
def _(formula: GloballyFormula):
    return GloballyFormula(
        formula.local_time,
        formula.global_time,
        to_unary_bounded_temporal_form(formula.child),
    )


@to_unary_bounded_temporal_form.register(UntilFormula)
def _(formula: UntilFormula):
    left = to_unary_bounded_temporal_form(formula.left)
    right = to_unary_bounded_temporal_form(formula.right)
    if formula.local_time == universeInterval:
        return UntilFormula(
            formula.local_time, formula.global_time, left, right
        )

    lower = formula.local_time.left
    continuation_interval = Interval(
        formula.local_time.left_end, RealVal("0.0"), False, RealVal("inf")
    )
    prefix_interval = Interval(True, RealVal("0.0"), True, lower)
    split_interval = Interval(True, lower, True, lower)
    return And([
        GloballyFormula(prefix_interval, formula.global_time, left),
        FinallyFormula(formula.local_time, formula.global_time, right),
        FinallyFormula(
            split_interval,
            formula.global_time,
            UntilFormula(
                continuation_interval, formula.global_time, left, right
            ),
        ),
    ])


@to_unary_bounded_temporal_form.register(ReleaseFormula)
def _(formula: ReleaseFormula):
    left = to_unary_bounded_temporal_form(formula.left)
    right = to_unary_bounded_temporal_form(formula.right)
    if formula.local_time == universeInterval:
        return ReleaseFormula(
            formula.local_time, formula.global_time, left, right
        )

    lower = formula.local_time.left
    continuation_interval = Interval(
        formula.local_time.left_end, RealVal("0.0"), False, RealVal("inf")
    )
    prefix_interval = Interval(True, RealVal("0.0"), True, lower)
    split_interval = Interval(True, lower, True, lower)
    return Or([
        FinallyFormula(prefix_interval, formula.global_time, left),
        GloballyFormula(formula.local_time, formula.global_time, right),
        GloballyFormula(
            split_interval,
            formula.global_time,
            ReleaseFormula(
                continuation_interval, formula.global_time, left, right
            ),
        ),
    ])


__all__ = ["to_unary_bounded_temporal_form"]
