"""Decode abstract scenario assignments into proposition and time paths."""

from functools import singledispatch
from typing import Dict, Set, Tuple

from ..constraints.constraints import (
    BinaryFormula, Bool, Eq, Formula, MultinaryFormula, NonLeaf, UnaryFormula,
)
from .fully_stable_stl import is_proposition
from .symbolic_ids import v_type1_info, v_type2_info


@singledispatch
def get_bools(formula: Formula) -> Set[Bool]:
    return set()


@get_bools.register(Bool)
def _(formula: Bool) -> Set[Bool]:
    return {formula}


@get_bools.register(UnaryFormula)
def _(formula: UnaryFormula) -> Set[Bool]:
    return get_bools(formula.child) if isinstance(formula, NonLeaf) else set()


@get_bools.register(BinaryFormula)
def _(formula: BinaryFormula) -> Set[Bool]:
    if isinstance(formula, (NonLeaf, Eq)):
        return get_bools(formula.left).union(get_bools(formula.right))
    return set()


@get_bools.register(MultinaryFormula)
def _(formula: MultinaryFormula) -> Set[Bool]:
    result = set()
    if isinstance(formula, NonLeaf):
        for child in formula.children:
            result.update(get_bools(child))
    return result


def _has_any(identifier: str, prefixes) -> bool:
    return any(prefix in identifier for prefix in prefixes)


def pick_time_and_props(unsat_cores: Set[str],
                        sub_formulas: Set[Formula]) -> Set[str]:
    """Keep core identifiers that contribute to model or proposition paths."""
    picked = set()
    for identifier in unsat_cores:
        is_chi = "chi" in identifier
        is_time_type1 = _has_any(identifier, ("T1", "T2", "T3"))
        if is_chi or is_time_type1:
            formula, _, _ = v_type1_info(identifier, sub_formulas)
            if is_proposition(formula):
                picked.add(identifier)

        if "T" in identifier and not is_time_type1:
            picked.add(identifier)
        if _has_any(identifier, ("invAtomicID", "newIntegral")):
            picked.add(identifier)
    return picked


def assn2path(unsat_cores: Set[str], sub_formulas: Set[Formula],
              tau_max: float) -> Tuple[
                  Dict[Tuple[int, Bool], Formula],
                  Dict[Tuple[int, Bool], Formula],
              ]:
    """Decode tracked Boolean names into proposition and time path maps."""
    path_dict = {}
    time_dict = {}
    for identifier in unsat_cores:
        is_chi = "chi" in identifier
        is_time_type1 = _has_any(identifier, ("T1", "T2", "T3"))
        if is_chi or is_time_type1:
            formula, _, depth = v_type1_info(identifier, sub_formulas)
            pair = (depth, Bool(identifier))
            if pair in path_dict:
                raise ValueError("duplicate path assignment: {}".format(pair))
            if is_proposition(formula):
                if is_chi:
                    path_dict[pair] = formula
                if is_time_type1:
                    time_dict[pair] = formula

        if "T" in identifier and not is_time_type1:
            formula, index = v_type2_info(identifier, tau_max)
            pair = (index, Bool(identifier))
            if not is_proposition(formula) or pair in path_dict:
                raise ValueError("invalid time path assignment: {}".format(pair))
            time_dict[pair] = formula
    return path_dict, time_dict


__all__ = ["assn2path", "get_bools", "pick_time_and_props"]

