"""Encoding of fully stable STL partitions (paper Definition 4.3).

This module is independent of the one-step and two-step solving strategies.
It builds ``Psi_PAR`` from the symbolic discrete-signal variables shared by
both algorithms.
"""

from typing import Dict, List, Set

from ..constraints.constraints import (
    And, Bool, BoolVal, Eq, FinallyFormula, Formula, GloballyFormula,
    Implies, Not, Or, ReleaseFormula, Sub, UntilFormula,
)
from ..constraints.interval import is_positive_infinity
from .fully_stable_stl import dependency_ordered_formulas
from .symbolic_discrete import chi, formula_id, symbolic_inf, symbolic_sup


def par_until(n: int, m: int, formula: Formula) -> Bool:
    return Bool("parU^{{{},{}}}_{}".format(n, m, formula_id(formula)))


def par_endpoint(kind: str, n: int, m: int, formula: Formula) -> Bool:
    return Bool("parEnd{}^{{{},{}}}_{}".format(
        kind, n, m, formula_id(formula)
    ))


def _temporal_operands(formula: Formula, index: int):
    """Return the Until operands used by Definition 4.3.

    F/G/R are handled through their standard Until duals, without rewriting
    the user's syntax tree and thereby changing the bounded partition size.
    """
    if isinstance(formula, UntilFormula):
        return chi(index, index, formula.left), chi(index, index, formula.right)
    if isinstance(formula, ReleaseFormula):
        return (Not(chi(index, index, formula.left)),
                Not(chi(index, index, formula.right)))
    if isinstance(formula, FinallyFormula):
        return BoolVal("True"), chi(index, index, formula.child)
    if isinstance(formula, GloballyFormula):
        return BoolVal("True"), Not(chi(index, index, formula.child))
    raise TypeError("not a temporal formula: {}".format(type(formula).__name__))


def _edge(value, previous=None, following=None):
    rising = value if previous is None else And([value, Not(previous)])
    falling = value if following is None else And([value, Not(following)])
    return rising, falling


def _endpoint_membership(value, index: int):
    return Or([
        Eq(value, symbolic_inf(index)), Eq(value, symbolic_sup(index))
    ])


def temporal_partition_obligations_at(
        formula: Formula, depth: int, horizon: int):
    """Yield Definition 4.3 obligations introduced at one signal depth."""
    interval = formula.local_time
    m = depth
    if m >= 1:
        left_m, right_m = _temporal_operands(formula, m)
        left_prev, right_prev = (
            _temporal_operands(formula, m - 1)
            if m > 1 else (None, None)
        )
        left_next, right_next = (
            _temporal_operands(formula, m + 1)
            if m < horizon else (None, None)
        )
        left_rise, left_fall = _edge(left_m, left_prev, left_next)
        right_rise, right_fall = _edge(right_m, right_prev, right_next)

        # U^(n,m) from Fig. 8.
        for n in range(m, 0, -1):
            chain = And([left_m, right_m]) if n == m else And([
                _temporal_operands(formula, n)[0],
                par_until(n + 1, m, formula),
            ])
            yield Eq(par_until(n, m, formula), chain)

        # Falling edge: r(J_m) - inf(I). Rising edge: l(J_m) - sup(I).
        candidates = [("fall",
                       Sub(symbolic_sup(m), interval.left),
                       Or([left_fall, right_fall]))]
        if not is_positive_infinity(interval.right):
            candidates.append((
                "rise", Sub(symbolic_inf(m), interval.right),
                Or([left_rise, right_rise]),
            ))

        for kind, value, edge_condition in candidates:
            candidate_parts = []
            for n in range(m, 0, -1):
                endpoint_here = _endpoint_membership(value, n)
                endpoint_suffix = endpoint_here if n == m else Or([
                    endpoint_here, par_endpoint(kind, n + 1, m, formula),
                ])
                yield Eq(
                    par_endpoint(kind, n, m, formula), endpoint_suffix
                )
                candidate_parts.append(Implies(
                    And([
                        par_until(n, m, formula),
                        symbolic_inf(n) <= value,
                    ]),
                    par_endpoint(kind, n, m, formula),
                ))
            yield Implies(edge_condition, And(candidate_parts))


def temporal_partition_obligations(formula: Formula, depth: int):
    """Yield ``cand`` and auxiliary definitions through ``depth``."""
    for current_depth in range(1, depth + 1):
        yield from temporal_partition_obligations_at(
            formula, current_depth, depth
        )


def partition_obligations(sub_formulas: Set[Formula], depth: int):
    obligations = []
    for formula in dependency_ordered_formulas(sub_formulas):
        if isinstance(formula, (
                UntilFormula, ReleaseFormula,
                FinallyFormula, GloballyFormula)):
            obligations.extend(
                temporal_partition_obligations(formula, depth)
            )
    return obligations


def fully_stable_partition_const(
        sub_formulas: Set[Formula], depth: int):
    """Build the strategy-independent ``Psi_PAR`` conjunction."""
    return And(partition_obligations(sub_formulas, depth))


class FullyStablePartitionEncoding:
    """Incrementally construct the strategy-independent Psi_PAR encoding."""

    def __init__(self, sub_formulas: Set[Formula]):
        # Define operand partitions before their enclosing temporal operator.
        self.sub_formulas = dependency_ordered_formulas(sub_formulas)
        self.depth = 0
        self.obligations_by_depth: Dict[int, List[Formula]] = {}

    def _obligations_at(self, depth: int, horizon: int) -> List[Formula]:
        obligations = []
        for formula in self.sub_formulas:
            if isinstance(formula, (
                    UntilFormula, ReleaseFormula,
                    FinallyFormula, GloballyFormula)):
                obligations.extend(temporal_partition_obligations_at(
                    formula, depth, horizon
                ))
        return obligations

    def extend_to(self, depth: int) -> Formula:
        if depth < self.depth:
            raise ValueError("partition depth cannot decrease")
        for current_depth in range(self.depth + 1, depth + 1):
            # The old horizon's final interval gains a following interval, so
            # only its falling-edge definition must be replaced. Earlier
            # depths are horizon-independent and remain reusable.
            if current_depth > 1:
                self.obligations_by_depth[current_depth - 1] = (
                    self._obligations_at(current_depth - 1, current_depth)
                )
            self.obligations_by_depth[current_depth] = self._obligations_at(
                current_depth, current_depth
            )
        self.depth = depth
        return self.formula()

    def formula(self) -> Formula:
        return And([
            obligation
            for depth in range(1, self.depth + 1)
            for obligation in self.obligations_by_depth[depth]
        ])
