from typing import Set

from ..robust.reduction import remove_binary
from ..robust.relaxing import weakening
from ....constraints.aux.operations import reduce_not, sub_formula
from ....constraints.constraints import *


def is_left_time(sub_formulas: Set[Formula]):
    for f in sub_formulas:
        if isinstance(f, UntilFormula) or isinstance(f, FinallyFormula):
            return True
    return False


def is_right_time(sub_formulas: Set[Formula]):
    for f in sub_formulas:
        if isinstance(f, ReleaseFormula) or isinstance(f, GloballyFormula):
            return True
    return False


def chi(i: int, k: int, f: Formula):
    return Bool("chi^{{{},{}}}_{}".format(i, k, hash(f)))


def t1(i: int, k: int, f: Formula):
    return Bool("T1^{{{},{}}}_{}".format(i, k, hash(f)))


def t2(i: int, k: int, f: Formula):
    return Bool("T2^{{{},{}}}_{}".format(i, k, hash(f)))


def t3(i: int, k: int, f: Formula):
    return Bool("T3^{{{},{}}}_{}".format(i, k, hash(f)))


def get_hash(v: Variable):
    return int(v.id.split("_")[1])


def get_chi_depth(v: Variable):
    return int(v.id.split(",")[1].split("}")[0])


def is_chi(v: Variable):
    return "chi^" in v.id


def is_time(v: Variable):
    return "T1^" in v.id or "T2^" in v.id or "T3^" in v.id


# sup(J_i)
def symbolic_sup(index: int) -> Real:
    # odd : [ \tau_{(i - 1) / 2}, \tau_{(i - 1) / 2} ]
    # even : ( \tau_{i / 2 - 1}, \tau_{i / 2} )
    tau_index = index / 2
    if index % 2 == 1:
        tau_index = (index - 1) / 2
    return Real("tau_{}".format(int(tau_index)))


# inf(J_i)
def symbolic_inf(index: int) -> Real:
    # odd : [ \tau_{(i - 1) / 2}, \tau_{(i - 1) / 2} ]
    # even : ( \tau_{i / 2 - 1}, \tau_{i / 2} )
    tau_index = index / 2 - 1
    if index % 2 == 1:
        tau_index = (index - 1) / 2
    return Real("tau_{}".format(int(tau_index)))


# final const
def final(f: Formula, depth: int):
    # chi^{{i, depth + 1}}_{f} = false
    # i \in [ 1 ... depth + 1 ]
    return And([chi(i, depth + 1, f) == BoolVal("False") for i in range(1, depth + 2)])


def time_ordering(n: int, tau_max: float) -> And:
    # n: even
    # 0 = \tau_0 < \tau_1 < ... < \tau_{i / 2} = \tau_max
    time_order: Set[Formula] = set()
    time_order.add(RealVal("0") == Real("tau_0"))
    time_order.add(symbolic_sup(n) == RealVal(str(tau_max)))

    for i in range(1, n, 2):
        time_order.add(Lt(symbolic_sup(i), symbolic_sup(i + 1)))

    return And(list(time_order))


def calc_sub_formulas(formula: Formula) -> Set[Formula]:
    sub_formulas = sub_formula(formula)
    new_formulas: Set[GloballyFormula] = set()

    for f in sub_formulas:
        if isinstance(f, FinallyFormula):
            local_time = Interval(True, RealVal("0.0"), f.local_time.left, False)
            new_formulas.add(GloballyFormula(local_time, f.global_time, f.child))
    return sub_formulas.union(new_formulas)


def strengthen_reduction(formula: Formula, threshold: float):
    negated_formula = reduce_not(Not(formula))
    reduced_formula = remove_binary(negated_formula)
    return weakening(reduced_formula, threshold)
