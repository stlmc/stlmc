from functools import singledispatch

from ...constraints.constraints import *


@singledispatch
def remove_binary(f: Formula):
    return f


@remove_binary.register(Not)
def _(f: Not):
    return Not(remove_binary(f.child))


@remove_binary.register(And)
def _(f: And):
    return And([remove_binary(c) for c in f.children])


@remove_binary.register(Or)
def _(f: Or):
    return Or([remove_binary(c) for c in f.children])


@remove_binary.register(Implies)
def _(f: Implies):
    return Implies(remove_binary(f.left), remove_binary(f.right))


@remove_binary.register(FinallyFormula)
def _(f: FinallyFormula):
    return FinallyFormula(f.local_time, f.global_time, remove_binary(f.child))


@remove_binary.register(GloballyFormula)
def _(f: GloballyFormula):
    return GloballyFormula(f.local_time, f.global_time, remove_binary(f.child))


@remove_binary.register(UntilFormula)
def _(f: UntilFormula):
    l, r = remove_binary(f.left), remove_binary(f.right)

    u = Interval(True, RealVal("0.0"), RealVal('inf'), False)
    if f.local_time == u:
        return UntilFormula(u, u, l, r)

    i0 = f.local_time
    i1 = Interval(True, i0.left, i0.right, True)
    i2 = Interval(True, RealVal("0.0"), i0.left, True)

    f1 = FinallyFormula(i1, u, r)
    f2 = GloballyFormula(i2, u, UntilFormula(u, u, l, r))

    return And([f1, f2])


@remove_binary.register(ReleaseFormula)
def _(f: ReleaseFormula):
    l, r = remove_binary(f.left), remove_binary(f.right)

    u = Interval(True, RealVal("0.0"), RealVal('inf'), False)
    if f.local_time == u:
        return ReleaseFormula(u, u, l, r)

    i0 = f.local_time
    i1 = Interval(True, i0.left, i0.right, True)
    i2 = Interval(True, RealVal("0.0"), i0.left, True)

    f1 = GloballyFormula(i1, u, r)
    f2 = FinallyFormula(i2, u, ReleaseFormula(u, u, l, r))

    return And([f1, f2])
