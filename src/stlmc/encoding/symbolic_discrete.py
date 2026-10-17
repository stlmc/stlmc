"""Strategy-independent symbolic discrete-signal primitives.

The paper's ``varsigma_(phi,n)`` representation is shared by Psi_STL,
Psi_PAR, one-step solving, and two-step solving.
"""

import hashlib

from ..constraints.constraints import (
    And, Bool, Eq, Formula, Interval, Real, RealVal,
)
from ..constraints.interval import is_positive_infinity


def ordered_formulas(formulas):
    """Preserve source order; canonicalize only unordered API inputs."""
    if isinstance(formulas, (set, frozenset)):
        return sorted(formulas, key=lambda f: (type(f).__qualname__, repr(f)))
    return formulas


def formula_id(formula: Formula) -> str:
    """Return a deterministic identifier for an immutable formula tree.

    Python's :func:`hash` is process-randomized and collisions used to merge
    unrelated temporal auxiliaries.  The concrete syntax includes every
    operator, interval, variable, and constant in these immutable trees; the
    node type prefix also separates formula classes with similar rendering.
    """
    cached = getattr(formula, "_stlmc_structural_id", None)
    if cached is not None:
        return cached
    structural_text = "{}:{}".format(
        type(formula).__qualname__, repr(formula)
    ).encode("utf-8")
    identifier = hashlib.sha256(structural_text).hexdigest()
    # Formula trees are treated as immutable throughout the encoders. Keeping
    # the digest on the root avoids repeatedly rendering large nested STL
    # formulas while constructing chi/rho/Psi_PAR at every depth.
    formula._stlmc_structural_id = identifier
    return identifier


def chi(i: int, k: int, formula: Formula) -> Bool:
    return Bool("chi^{{{},{}}}_{}".format(i, k, formula_id(formula)))


def rho(i: int, n: int, formula: Formula) -> Bool:
    return Bool("rho^{{{},{}}}_{}".format(i, n, formula_id(formula)))


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
    # Repeated endpoints create an empty open flow interval. Its midpoint
    # exists arithmetically, but it cannot witness any temporal operator.
    if scan % 2 == 0:
        conditions.append(symbolic_inf(scan) < symbolic_sup(scan))
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
    constraints = [
        Eq(RealVal("0"), Real("tau_0")),
    ]
    for index in range(1, depth, 2):
        current = symbolic_sup(index)
        following = symbolic_sup(index + 1)
        constraints.append(
            current < following if index == depth - 1
            else current <= following
        )
    constraints.append(Eq(symbolic_sup(depth), RealVal(str(tau_max))))
    return And(constraints)


def reach_time_ordering(depth: int, tau_max: float) -> And:
    constraints = [
        Eq(RealVal("0"), Real("tau_0")),
    ]
    for index in range(1, depth, 2):
        constraints.append(symbolic_sup(index) < symbolic_sup(index + 1))
    constraints.append(symbolic_sup(depth) <= RealVal(str(tau_max)))
    return And(constraints)
