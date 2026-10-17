"""Constraint-tree helpers used while constructing solver encodings."""

from functools import singledispatch
from itertools import combinations

from .constraints import (
    And, Bool, Constraint, Eq, FinallyFormula, Formula, GloballyFormula,
    Implies, Neq, Not, Or, ReleaseFormula, UntilFormula,
)


@singledispatch
def clause(const: Constraint):
    return {const}


@clause.register(Not)
@clause.register(FinallyFormula)
@clause.register(GloballyFormula)
def _(const):
    return clause(const.child)


@clause.register(And)
@clause.register(Or)
def _(const):
    result = set()
    for child in const.children:
        result.update(clause(child))
    return result


@clause.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Formula):
        return clause(const.left) | clause(const.right)
    return {const}


@clause.register(Implies)
@clause.register(UntilFormula)
@clause.register(ReleaseFormula)
def _(const):
    return clause(const.left) | clause(const.right)


def ordered_clause(const):
    """The same clause leaves as clause(), in source traversal order."""
    result = dict()
    pending = [const]
    while pending:
        current = pending.pop()
        if isinstance(current, (Not, FinallyFormula, GloballyFormula)):
            pending.append(current.child)
        elif isinstance(current, (And, Or)):
            pending.extend(reversed(current.children))
        elif (isinstance(current, (Implies, UntilFormula, ReleaseFormula))
              or isinstance(current, Eq) and isinstance(current.left, Formula)):
            pending.extend([current.right, current.left])
        else:
            result[current] = None
    return tuple(result)


def lower_encoding(chi, bound, lower):
    adjacent_pairs = [
        (chi + "_" + str(index), chi + "_" + str(index + 1))
        for index in range(1, 2 * (bound + 1))
    ]
    result = []
    for selected_pairs in combinations(adjacent_pairs, lower):
        selected = set(selected_pairs)
        constraints = [
            Neq(Bool(left), Bool(right))
            if (left, right) in selected
            else Eq(Bool(left), Bool(right))
            for left, right in adjacent_pairs
        ]
        result.append(And(constraints))
    return Or(result)
