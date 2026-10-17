"""Strategy-independent encoding of paper Definition 4.2 (Psi_STL)."""

from typing import Set, Tuple

from ..constraints.constraints import (
    And, BinaryFormula, Bool, BoolVal, Eq, FinallyFormula, Formula,
    GloballyFormula, Leaf, MultinaryFormula, Not, Or, ReleaseFormula,
    UnaryFormula, UntilFormula, Variable,
)
from ..constraints.logical_normalization import reduce_not
from ..constraints.robustness_transform import strengthening
from ..constraints.substitution import substitution
from ..constraints.temporal_rewrite import to_unary_bounded_temporal_form
from ..exceptions import IllegalArgumentError, NotSupportedError
from ..objects.goal import Goal
from .symbolic_discrete import (
    chi, rho, symbolic_inf, symbolic_sup, temporal_candidate,
)


def is_proposition(formula: Formula) -> bool:
    return isinstance(formula, Bool) or (
        not isinstance(formula, Variable) and isinstance(formula, Leaf)
    )


def sub_formula(formula: Formula) -> Set[Formula]:
    """Return the structural subformula closure used by Psi_STL/Psi_PAR."""
    if not isinstance(formula, Formula):
        raise TypeError("expected an STL formula")
    result = {formula}
    pending = [formula]
    while pending:
        current = pending.pop()
        if is_proposition(current):
            continue
        if isinstance(current, UnaryFormula):
            children = [current.child]
        elif isinstance(current, BinaryFormula):
            children = [current.left, current.right]
        elif isinstance(current, MultinaryFormula):
            children = list(current.children)
        else:
            continue
        for child in children:
            if child not in result:
                result.add(child)
                pending.append(child)
    return result


def calc_sub_formulas(formula: Formula) -> Set[Formula]:
    return sub_formula(formula)


def final(formula: Formula, depth: int) -> Formula:
    terminal = None
    if isinstance(formula, (UntilFormula, FinallyFormula)):
        terminal = BoolVal("False")
    elif isinstance(formula, (ReleaseFormula, GloballyFormula)):
        terminal = BoolVal("True")
    if terminal is None:
        return And([])
    return And([
        Eq(rho(index, depth + 1, formula), terminal)
        for index in range(1, depth + 1)
    ])


def symbolic_goal(formula: Formula, start: int, depth: int, tau_max):
    del tau_max  # retained in the public signature for compatibility
    if isinstance(formula, And):
        assert start == depth
        return Eq(chi(start, depth, formula), And([
            chi(start, start, child) for child in formula.children
        ]))
    if isinstance(formula, Or):
        assert start == depth
        return Eq(chi(start, depth, formula), Or([
            chi(start, start, child) for child in formula.children
        ]))
    if isinstance(formula, UntilFormula):
        step = Or([
            And([
                temporal_candidate(start, depth, formula.local_time),
                chi(depth, depth, formula.left),
                chi(depth, depth, formula.right),
            ]),
            And([
                chi(depth, depth, formula.left),
                rho(start, depth + 1, formula),
            ]),
        ])
    elif isinstance(formula, ReleaseFormula):
        candidate = temporal_candidate(start, depth, formula.local_time)
        step = And([
            Or([
                Not(candidate), chi(depth, depth, formula.left),
                chi(depth, depth, formula.right),
            ]),
            Or([
                chi(depth, depth, formula.left),
                rho(start, depth + 1, formula),
            ]),
        ])
    elif isinstance(formula, GloballyFormula):
        candidate = temporal_candidate(start, depth, formula.local_time)
        step = And([
            Or([Not(candidate), chi(depth, depth, formula.child)]),
            rho(start, depth + 1, formula),
        ])
    elif isinstance(formula, FinallyFormula):
        step = Or([
            And([
                temporal_candidate(start, depth, formula.local_time),
                chi(depth, depth, formula.child),
            ]),
            rho(start, depth + 1, formula),
        ])
    else:
        raise NotSupportedError("cannot find related rule")
    if depth % 2 == 0 and isinstance(formula, (UntilFormula, ReleaseFormula)):
        # An empty interval contributes neither a witness nor an operand
        # obligation. Skip it in the recurrence, preserving U/R duality.
        nonempty = symbolic_inf(depth) < symbolic_sup(depth)
        step = Or([
            And([Not(nonempty), rho(start, depth + 1, formula)]),
            And([nonempty, step]),
        ])
    return And([
        Eq(rho(start, depth, formula), step),
        Eq(chi(start, start, formula), rho(start, start, formula))
        if start == depth else BoolVal("True"),
    ])


def k_depth_stl_consts(
        sub_formulas: Set[Formula], depth: int,
        tau_max: float) -> Tuple[Formula, Formula, Formula]:
    goal_consts = set()
    for formula in sub_formulas:
        if is_proposition(formula):
            continue
        if isinstance(formula, (
                FinallyFormula, GloballyFormula,
                UntilFormula, ReleaseFormula)):
            goal_consts.update(
                symbolic_goal(formula, start, depth, tau_max)
                for start in range(1, depth + 1)
            )
        else:
            goal_consts.add(symbolic_goal(
                formula, depth, depth, tau_max
            ))
    return (
        And(list(goal_consts)),
        BoolVal("True"),
        And([final(formula, depth) for formula in sub_formulas]),
    )


def prepare_fully_stable_stl_formula(
        goal: Goal, goal_prop_dict, delta: float,
        use_unary_bounded_temporal_form: bool = False) -> Formula:
    """Build ``not(phi^+epsilon)`` for the common Boolean STL encoding."""
    raw_formula = substitution(goal.get_formula(), goal_prop_dict)
    strengthened_formula = strengthening(raw_formula, delta)
    counterexample_formula = reduce_not(Not(strengthened_formula))
    if use_unary_bounded_temporal_form:
        return to_unary_bounded_temporal_form(counterexample_formula)
    return counterexample_formula


def stl_depth_components(sub_formulas: Set[Formula], depths, tau_max: float):
    stl_children = []
    time_children = []
    terminal = None
    for depth in depths:
        stl_const, time_const, terminal = k_depth_stl_consts(
            sub_formulas, depth, tau_max
        )
        stl_children.append(stl_const)
        time_children.append(time_const)
    if terminal is None:
        raise IllegalArgumentError("at least one STL depth is required")
    return stl_children, time_children, terminal
