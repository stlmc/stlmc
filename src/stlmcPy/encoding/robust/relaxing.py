from functools import singledispatch
from typing import Union

from ...constraints.aux.generator import *
from ...constraints.constraints import *


@singledispatch
def weakening(const: Union[Formula, Expr], threshold: float):
    return const


@weakening.register(UnaryFormula)
def _(const: UnaryFormula, threshold: float):
    return unary_formula(weakening(const.child, threshold), const.type)


@weakening.register(BinaryFormula)
def _(const: BinaryFormula, threshold: float):
    return binary_formula(weakening(const.left, threshold), weakening(const.right, threshold), const.type)


@weakening.register(MultinaryFormula)
def _(const: MultinaryFormula, threshold: float):
    return multinary_formula([weakening(c, threshold) for c in const.children], const.type)


@weakening.register(Geq)
def _(const: Geq, threshold: float):
    return Geq(const.left, const.right - RealVal(str(threshold)))


@weakening.register(Gt)
def _(const: Gt, threshold: float):
    return Gt(const.left, const.right - RealVal(str(threshold)))


@weakening.register(Leq)
def _(const: Leq, threshold: float):
    return Leq(const.left, const.right + RealVal(str(threshold)))


@weakening.register(Lt)
def _(const: Lt, threshold: float):
    return Lt(const.left, const.right + RealVal(str(threshold)))


@weakening.register(Eq)
def _(const: Eq, threshold: float):
    half = RealVal(str(threshold)) / RealVal('2')
    return And([const.left >= const.right - half, const.left <= const.right + half])


@weakening.register(Neq)
def _(const: Neq, threshold: float):
    half = RealVal(str(threshold)) / RealVal('2')
    return Or([const.left <= const.right - half, const.left >= const.right + half])


@weakening.register(UnaryTemporalFormula)
def _(const: UnaryTemporalFormula, threshold: float):
    child = weakening(const.child, threshold)
    return unary_temporal_formula(const.local_time, const.global_time, child, const.type)


@weakening.register(BinaryTemporalFormula)
def _(const: BinaryTemporalFormula, threshold: float):
    left = weakening(const.left, threshold)
    right = weakening(const.right, threshold)
    return binary_temporal_formula(const.local_time, const.global_time, left, right, const.type)


@singledispatch
def strengthening(const: Union[Formula, Expr], threshold: float):
    return const


@strengthening.register(UnaryFormula)
def _(const: UnaryFormula, threshold: float):
    return unary_formula(strengthening(const.child, threshold), const.type)


@strengthening.register(BinaryFormula)
def _(const: BinaryFormula, threshold: float):
    return binary_formula(strengthening(const.left, threshold), strengthening(const.right, threshold), const.type)


@strengthening.register(MultinaryFormula)
def _(const: MultinaryFormula, threshold: float):
    return multinary_formula([strengthening(c, threshold) for c in const.children], const.type)


@strengthening.register(Geq)
def _(const: Geq, threshold: float):
    return Geq(const.left, const.right + RealVal(str(threshold)))


@strengthening.register(Gt)
def _(const: Gt, threshold: float):
    return Gt(const.left, const.right + RealVal(str(threshold)))


@strengthening.register(Leq)
def _(const: Leq, threshold: float):
    return Leq(const.left, const.right - RealVal(str(threshold)))


@strengthening.register(Lt)
def _(const: Lt, threshold: float):
    return Lt(const.left, const.right - RealVal(str(threshold)))


@strengthening.register(Eq)
def _(const: Eq, threshold: float):
    half = RealVal(str(threshold)) / RealVal('2')
    return And([const.left >= const.right + half, const.left <= const.right - half])


@strengthening.register(Neq)
def _(const: Neq, threshold: float):
    half = RealVal(str(threshold)) / RealVal('2')
    return Or([const.left <= const.right + half, const.left >= const.right - half])


@strengthening.register(UnaryTemporalFormula)
def _(const: UnaryTemporalFormula, threshold: float):
    child = strengthening(const.child, threshold)
    return unary_temporal_formula(const.local_time, const.global_time, child, const.type)


@strengthening.register(BinaryTemporalFormula)
def _(const: BinaryTemporalFormula, threshold: float):
    left = strengthening(const.left, threshold)
    right = strengthening(const.right, threshold)
    return binary_temporal_formula(const.local_time, const.global_time, left, right, const.type)
