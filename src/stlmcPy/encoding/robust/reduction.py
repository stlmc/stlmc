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
    universeInterval = Interval(True, RealVal("0.0"), RealVal('inf'), False)
    if f.local_time == universeInterval:
        return f

    left_interval = f.local_time.left_end
    left_time = f.local_time.left
    right_interval = f.local_time.right_end
    right_time = f.local_time.right

    right = remove_binary(f.right)
    left = remove_binary(f.left)

    right_formula = FinallyFormula(Interval(left_interval, left_time, right_time, right_interval), f.global_time, right)

    if left_interval:
        left_formula_1 = GloballyFormula(Interval(False, RealVal("0"), left_time, False), f.global_time, left)
        subFormula = Or([right, And([left, UntilFormula(universeInterval, f.global_time, left, right)])])
        left_formula_2 = GloballyFormula(Interval(False, RealVal("0"), left_time, True), f.global_time, subFormula)
        return And([And([left_formula_1, left_formula_2]), right_formula])
    else:
        subFormula = And([left, UntilFormula(universeInterval, f.global_time, left, right)])
        final_left = GloballyFormula(Interval(False, RealVal("0"), left_time, True), f.global_time, subFormula)
        return And([final_left, right_formula])


@remove_binary.register(ReleaseFormula)
def _(f: ReleaseFormula):
    universeInterval = Interval(True, RealVal("0.0"), RealVal('inf'), False)
    if f.local_time == universeInterval:
        return f

    left_interval = f.local_time.left_end
    left_time = f.local_time.left
    right_interval = f.local_time.right_end
    right_time = f.local_time.right

    right = remove_binary(f.right)
    left = remove_binary(f.left)

    right_formula = GloballyFormula(Interval(left_interval, left_time, right_time, right_interval), f.global_time,
                                    right)

    if left_interval:
        left_formula_1 = FinallyFormula(Interval(False, RealVal("0"), left_time, False), f.global_time, left)
        subFormula = And([right, Or([left, ReleaseFormula(universeInterval, f.global_time, left, right)])])
        left_formula_2 = FinallyFormula(Interval(False, RealVal("0"), left_time, True), f.global_time, subFormula)
        return Or([And([left_formula_1, left_formula_2]), right_formula])
    else:
        subFormula = Or([left, ReleaseFormula(universeInterval, f.global_time, left, right)])
        final_left = FinallyFormula(Interval(False, RealVal("0"), left_time, True), f.global_time, subFormula)
        return Or([final_left, right_formula])
