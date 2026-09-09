"""Boolean abstraction helpers for quantified and integral constraints."""

from functools import singledispatch

from .constraints import (
    And, Binary, Bool, Constraint, Eq, Forall, Implies, Integral, Multinary,
    Neq, Not, Or, Unary,
)


@singledispatch
def get_boolean_abstraction(const: Constraint):
    return set()


@get_boolean_abstraction.register(Forall)
@get_boolean_abstraction.register(Integral)
def _(const):
    return {const}


@get_boolean_abstraction.register(Unary)
def _(const: Unary):
    return get_boolean_abstraction(const.child)


@get_boolean_abstraction.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Forall) or isinstance(const.right, Forall):
        return {const}
    if isinstance(const.left, Bool) and "newTau#" in const.left.id:
        return {const}
    return set()


@get_boolean_abstraction.register(Binary)
def _(const: Binary):
    return (
        get_boolean_abstraction(const.left)
        | get_boolean_abstraction(const.right)
    )


@get_boolean_abstraction.register(Multinary)
def _(const: Multinary):
    result = set()
    for child in const.children:
        result.update(get_boolean_abstraction(child))
    return result


@singledispatch
def forall_integral_substitution(const: Constraint, substitution_dict):
    return const


@forall_integral_substitution.register(And)
def _(const: And, substitution_dict):
    return And([
        forall_integral_substitution(child, substitution_dict)
        for child in const.children
    ])


@forall_integral_substitution.register(Or)
def _(const: Or, substitution_dict):
    return Or([
        forall_integral_substitution(child, substitution_dict)
        for child in const.children
    ])


@forall_integral_substitution.register(Not)
def _(const: Not, substitution_dict):
    return Not(forall_integral_substitution(const.child, substitution_dict))


@forall_integral_substitution.register(Eq)
@forall_integral_substitution.register(Forall)
@forall_integral_substitution.register(Integral)
def _(const, substitution_dict):
    return substitution_dict.get(const, const)


@forall_integral_substitution.register(Neq)
@forall_integral_substitution.register(Implies)
def _(const, substitution_dict):
    return type(const)(
        forall_integral_substitution(const.left, substitution_dict),
        forall_integral_substitution(const.right, substitution_dict),
    )


def inverse_dict(original_dict: dict):
    return {value: key for key, value in original_dict.items()}


def generate_id(initial, gid="v"):
    counter = initial
    while True:
        yield gid + str(counter)
        counter += 1


def make_boolean_abstract_consts(props: dict):
    variables = sorted(props, key=lambda variable: variable.id)
    return And([Eq(variable, props[variable]) for variable in variables])
