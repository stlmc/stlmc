"""Bounded STL formula assembly shared by all solving strategies."""

from typing import Set

from ..constraints.constraints import And, Formula
from ..encoding.fully_stable_partition import FullyStablePartitionEncoding
from ..encoding.fully_stable_stl import (
    calc_sub_formulas, is_proposition, prepare_fully_stable_stl_formula,
    stl_depth_components,
)
from ..encoding.symbolic_discrete import chi, time_ordering
from ..encoding.model_linking import path2const
from ..objects.goal import Goal
from ..objects.model import Model


def bounded_proposition_matching(model: Model, sub_formulas: Set[Formula],
                                 depth: int) -> Formula:
    """Retain Fig. 9 matching for every atomic truth value, not only true cores."""
    return path2const({
        (index, chi(index, index, proposition)): proposition
        for proposition in sub_formulas if is_proposition(proposition)
        for index in range(1, depth + 1)
    }, model)


def bounded_stl_formula(model: Model, goal: Goal, goal_prop_dict, bound: int,
                        delta: float, tau_max: float,
                        use_unary_bounded_temporal_form: bool = False) -> Formula:
    """Build the complete bounded STL formula used by either strategy."""
    shifted_formula = prepare_fully_stable_stl_formula(
        goal, goal_prop_dict, delta, use_unary_bounded_temporal_form
    )
    return bounded_stl_formula_from_threshold(
        model, shifted_formula, bound, tau_max
    )


def bounded_stl_formula_from_threshold(
        model: Model, shifted_formula: Formula, bound: int,
        tau_max: float) -> Formula:
    """Build a bounded encoding for an already threshold-shifted formula."""
    sub_formulas = calc_sub_formulas(shifted_formula)
    max_depth = 2 * (bound + 1)
    stl_children, time_children, terminal = stl_depth_components(
        sub_formulas, range(1, max_depth + 1), tau_max
    )
    path_children = [chi(1, 1, shifted_formula)]
    path_children.extend(stl_children)
    path_children.extend(time_children)
    path_children.append(time_ordering(max_depth, tau_max))

    proposition_constraints = bounded_proposition_matching(
        model, sub_formulas, max_depth
    )

    partition = FullyStablePartitionEncoding(sub_formulas)
    partition.extend_to(max_depth)
    return And(path_children + [
        terminal, partition.formula(), proposition_constraints,
    ])


# Compatibility names used by the former monolithic/two-step modules.
k_size_stl_formula = bounded_stl_formula
k_size_stl_formula_from_threshold = bounded_stl_formula_from_threshold


__all__ = [
    "bounded_proposition_matching", "bounded_stl_formula",
    "bounded_stl_formula_from_threshold",
    "k_size_stl_formula", "k_size_stl_formula_from_threshold",
]
