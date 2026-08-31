"""Decode symbolic STL identifiers and rename formulas to model bounds."""

from typing import Set, Tuple

from ..constraints.constraints import (
    Add, Bool, Eq, FinallyFormula, Formula, GloballyFormula, Leq, Real,
    RealVal, Sub,
)
from ..constraints.operations import get_vars, substitution
from ..encoding.symbolic_discrete import (
    formula_id, symbolic_inf, symbolic_sup,
)
from ..exceptions import NotSupportedError


def type1_index_info(variable_id: str) -> Tuple[int, int]:
    encoded_indices = variable_id.split("_")[0].split("^")[1][1:-1]
    indices = encoded_indices.split(",")
    if len(indices) != 2:
        raise ValueError("invalid type-1 symbolic identifier: {}".format(
            variable_id
        ))
    return int(indices[0]), int(indices[1])


def type2_index_info(variable_id: str) -> int:
    return int(variable_id.split("_")[0].split("^")[1])


def inv_index_info(variable_id: str) -> Tuple[int, int]:
    parts = variable_id.split("_")
    return int(parts[1][0]), int(parts[2])


def type1_info(variable_id: str, sub_formulas: Set[Formula]
               ) -> Tuple[Formula, int, int]:
    structural_id = variable_id.split("_", 1)[1]
    formula_index, depth = type1_index_info(variable_id)
    for formula in sub_formulas:
        if formula_id(formula) == structural_id:
            return formula, formula_index, depth
    raise NotSupportedError("cannot find corresponding formula")


def type2_info(variable_id: str, tau_max: float) -> Tuple[Formula, int]:
    side = variable_id.split("_")[1]
    index = type2_index_info(variable_id)
    if side == "l":
        return symbolic_sup(index) <= RealVal(str(tau_max)), index
    if side == "r":
        return Eq(symbolic_sup(index), RealVal(str(tau_max))), index
    raise NotSupportedError("cannot find corresponding formula")


def v_type1_info(variable_id: str, sub_formulas: Set[Formula]
                 ) -> Tuple[Formula, int, int]:
    if "chi" in variable_id:
        return type1_info(variable_id, sub_formulas)

    formula, formula_index, depth = type1_info(variable_id, sub_formulas)
    if not isinstance(formula, (GloballyFormula, FinallyFormula)):
        raise NotSupportedError(
            "time identifiers require a unary temporal formula"
        )

    upper = formula.local_time.right
    lower = formula.local_time.left
    if "T1" in variable_id:
        return Leq(symbolic_sup(depth),
                   Add(symbolic_inf(formula_index), lower)), formula_index, depth
    if "T2" in variable_id:
        return Leq(Add(symbolic_sup(formula_index), upper),
                   symbolic_inf(depth)), formula_index, depth
    if "T3" in variable_id:
        return Leq(Sub(symbolic_inf(depth), upper),
                   symbolic_inf(formula_index)), formula_index, depth
    raise NotSupportedError("unknown time type")


def v_type2_info(variable_id: str, tau_max: float) -> Tuple[Formula, int]:
    return type2_info(variable_id, tau_max)


def rename(formula: Formula, bound: int, is_vertex=True):
    rename_dict = {}
    for variable in get_vars(formula):
        if isinstance(variable, Bool):
            rename_dict[variable] = Bool("{}_{}".format(variable.id, bound))
        elif isinstance(variable, Real) and "tau_" not in variable.id:
            if is_vertex or bound == 0:
                suffix = "{}_0".format(bound)
            else:
                suffix = "{}_t".format(bound - 1)
            rename_dict[variable] = Real("{}_{}".format(variable.id, suffix))
    return substitution(formula, rename_dict), rename_dict


def depth2bound(depth: int) -> int:
    return int((depth - 1) / 2)


__all__ = [
    "depth2bound", "inv_index_info", "rename", "type1_index_info",
    "type1_info", "type2_index_info", "type2_info", "v_type1_info",
    "v_type2_info",
]
