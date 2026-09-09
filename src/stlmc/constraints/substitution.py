"""Structure-preserving substitution over constraint trees."""

from functools import singledispatch

from .constraints import (
    Add, And, Constraint, Div, Eq, FinallyFormula, Forall, Function, Geq,
    GloballyFormula, Gt, Implies, Leq, Lt, Mul, Neg, Neq, Not, Ode, Or, Pow,
    ReleaseFormula, Sub, UnaryExpr, UntilFormula, Variable,
)


@singledispatch
def substitution(const: Constraint, substitution_dict):
    return const


@substitution.register(UnaryExpr)
def _(const: UnaryExpr, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return type(const)(substitution(const.child, substitution_dict))


@substitution.register(Variable)
def _(const: Variable, substitution_dict):
    return substitution_dict.get(const, const)


def _substitute_binary(const, substitution_dict):
    return (
        substitution(const.left, substitution_dict),
        substitution(const.right, substitution_dict),
    )


@substitution.register(Add)
def _(const: Add, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Add(*_substitute_binary(const, substitution_dict))


@substitution.register(Sub)
def _(const: Sub, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Sub(*_substitute_binary(const, substitution_dict))


@substitution.register(Mul)
def _(const: Mul, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Mul(*_substitute_binary(const, substitution_dict))


@substitution.register(Div)
def _(const: Div, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Div(*_substitute_binary(const, substitution_dict))


@substitution.register(Pow)
def _(const: Pow, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Pow(*_substitute_binary(const, substitution_dict))


@substitution.register(Neg)
def _(const: Neg, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Neg(substitution(const.child, substitution_dict))


@substitution.register(Function)
def _(const: Function, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Function(
        [substitution(var, substitution_dict) for var in const.vars],
        [substitution(exp, substitution_dict) for exp in const.exps],
    )


@substitution.register(Ode)
def _(const: Ode, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Ode(
        [substitution(var, substitution_dict) for var in const.vars],
        [substitution(exp, substitution_dict) for exp in const.exps],
    )


@substitution.register(And)
def _(const: And, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return And([substitution(child, substitution_dict) for child in const.children])


@substitution.register(Or)
def _(const: Or, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Or([substitution(child, substitution_dict) for child in const.children])


@substitution.register(Not)
def _(const: Not, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Not(substitution(const.child, substitution_dict))


def _substitute_comparison(const, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return type(const)(
        substitution(const.left, substitution_dict),
        substitution(const.right, substitution_dict),
        const.is_range,
    )


substitution.register(Gt)(_substitute_comparison)
substitution.register(Geq)(_substitute_comparison)
substitution.register(Lt)(_substitute_comparison)
substitution.register(Leq)(_substitute_comparison)
substitution.register(Eq)(_substitute_comparison)


@substitution.register(Neq)
def _(const: Neq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Neq(*_substitute_binary(const, substitution_dict))


@substitution.register(Implies)
def _(const: Implies, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Implies(*_substitute_binary(const, substitution_dict))


@substitution.register(Forall)
def _(const: Forall, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Forall(
        const.current_mode_number, const.end_tau, const.start_tau,
        substitution(const.const, substitution_dict), const.integral,
    )


def _substitute_unary_temporal(const, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return type(const)(
        const.local_time, const.global_time,
        substitution(const.child, substitution_dict),
    )


substitution.register(FinallyFormula)(_substitute_unary_temporal)
substitution.register(GloballyFormula)(_substitute_unary_temporal)


def _substitute_binary_temporal(const, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return type(const)(
        const.local_time, const.global_time,
        substitution(const.left, substitution_dict),
        substitution(const.right, substitution_dict),
    )


substitution.register(UntilFormula)(_substitute_binary_temporal)
substitution.register(ReleaseFormula)(_substitute_binary_temporal)
