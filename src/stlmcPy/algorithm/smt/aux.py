from functools import singledispatch

from ...constraints.constraints import *


def depth2bound(depth: int):
    return int((depth - 1) / 2)


@singledispatch
def literals(const: Formula):
    return {const}


@literals.register(BoolVal)
def _(const: BoolVal):
    return {}


@literals.register(UnaryFormula)
def _(const: UnaryFormula):
    return literals(const.child)


@literals.register(BinaryFormula)
def _(const: BinaryFormula):
    return literals(const.left).union(literals(const.right))


@literals.register(MultinaryFormula)
def _(const: MultinaryFormula):
    literal_set = set()
    for c in const.children:
        literal_set.update(literals(c))
    return literal_set


def print_bound(num_scenarios_at_bound):
    print()
    print("# total")
    for b, n in enumerate(num_scenarios_at_bound):
        print("  scenarios@{} = {}".format(b, n))
