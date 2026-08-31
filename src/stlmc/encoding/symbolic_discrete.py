"""Strategy-independent symbolic discrete-signal primitives.

The paper's ``varsigma_(phi,n)`` representation is shared by Psi_STL,
Psi_PAR, one-step solving, and two-step solving.
"""

from ..constraints.constraints import (
    And, Bool, Eq, Formula, Interval, Real, RealVal,
)
from ..constraints.interval import is_positive_infinity


def chi(i: int, k: int, formula: Formula) -> Bool:
    return Bool("chi^{{{},{}}}_{}".format(i, k, hash(formula)))


def rho(i: int, n: int, formula: Formula) -> Bool:
    return Bool("rho^{{{},{}}}_{}".format(i, n, hash(formula)))


def symbolic_sup(index: int) -> Real:
    tau_index = index / 2
    if index % 2 == 1:
        tau_index = (index - 1) / 2
    return Real("tau_{}".format(int(tau_index)))


def symbolic_inf(index: int) -> Real:
    tau_index = index / 2 - 1
    if index % 2 == 1:
        tau_index = (index - 1) / 2
    return Real("tau_{}".format(int(tau_index)))


def symbolic_interval(index: int) -> Interval:
    point = index % 2 == 1
    return Interval(point, symbolic_inf(index), point, symbolic_sup(index))


def temporal_candidate(start: int, scan: int, interval: Interval):
    """Encode midpoint(J_start) membership in J_scan - interval."""
    from ..constraints.constraints import Add, Div, Sub

    start_interval = symbolic_interval(start)
    scan_interval = symbolic_interval(scan)
    midpoint = Div(
        Add(start_interval.left, start_interval.right), RealVal("2.0")
    )
    conditions = []
    if not is_positive_infinity(interval.right):
        lower = Sub(scan_interval.left, interval.right)
        conditions.append(
            midpoint >= lower
            if scan_interval.left_end and interval.right_end
            else midpoint > lower
        )
    upper = Sub(scan_interval.right, interval.left)
    conditions.append(
        midpoint <= upper
        if scan_interval.right_end and interval.left_end
        else midpoint < upper
    )
    return And(conditions)


def time_ordering(depth: int, tau_max: float) -> And:
    """Paper ordering 0=tau_0<=...<=tau_(n-1)<tau_n=tau_max."""
    constraints = {
        Eq(RealVal("0"), Real("tau_0")),
        Eq(symbolic_sup(depth), RealVal(str(tau_max))),
    }
    for index in range(1, depth, 2):
        current = symbolic_sup(index)
        following = symbolic_sup(index + 1)
        constraints.add(
            current < following if index == depth - 1
            else current <= following
        )
    return And(list(constraints))


def reach_time_ordering(depth: int, tau_max: float) -> And:
    constraints = {
        Eq(RealVal("0"), Real("tau_0")),
        symbolic_sup(depth) <= RealVal(str(tau_max)),
    }
    for index in range(1, depth, 2):
        constraints.add(symbolic_sup(index) < symbolic_sup(index + 1))
    return And(list(constraints))
