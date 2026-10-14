"""Translate abstract scenario paths and cores into model constraints."""

from typing import Dict, Set, Tuple

from ..constraints.constraints import (
    And, Bool, Eq, Forall, Formula, Not, Or, Real, RealVal,
)
from .fully_stable_stl import is_proposition
from .symbolic_discrete import symbolic_inf, symbolic_sup
from ..objects.model import Model
from .symbolic_ids import depth2bound, rename, v_type1_info


Path = Dict[Tuple[int, Bool], Formula]


def is_mode_variable(variable: Bool, model: Model) -> bool:
    return variable.id in model.mode_var_dict


def _tracked_variable(variable: Bool) -> Bool:
    return Bool(variable.id.replace("p@", ""))


def path2const(path: Path, model: Model) -> Formula:
    """Bind proposition path literals to model states and flows."""
    constraints = []
    for (depth, variable), formula in path.items():
        bound = depth2bound(depth)
        is_vertex = depth % 2 == 0
        renamed, _ = rename(formula, bound, is_vertex)
        tracked = _tracked_variable(variable)

        if not is_vertex:
            renamed_edge, _ = rename(formula, bound, False)
            constraints.append(Eq(tracked, renamed_edge))
            continue
        if is_mode_variable(variable, model):
            renamed_edge, _ = rename(formula, bound, False)
            constraints.append(Eq(tracked, renamed_edge))
            continue

        modes = []
        for module_index, _ in enumerate(model.modules):
            integral = model.boolean_abstract[
                Bool("newIntegral_{}_{}".format(module_index, bound))
            ]
            forall = Forall(
                module_index, symbolic_sup(depth), symbolic_inf(depth),
                renamed, integral,
            )
            forall_negative = Forall(
                module_index, symbolic_sup(depth), symbolic_inf(depth),
                Not(renamed), integral,
            )
            matching = Eq(
                Real("currentMode_{}".format(bound)),
                RealVal(str(module_index)),
            )
            # Fig. 11: both Boolean values must match the entire open
            # flow interval. Negating a universal positive condition only
            # requires one false point and does not enforce stability.
            # The excluded start endpoint is constrained separately.
            modes.append(And([matching, Or([
                # The paper permits repeated partition endpoints. Universal
                # matching on the resulting empty open interval is vacuous.
                Eq(symbolic_sup(depth), symbolic_inf(depth)),
                And([tracked, forall]),
                And([Not(tracked), forall_negative]),
            ])]))
        constraints.append(Or(modes))
    return And(constraints)


def time_path2const(path: Path) -> Formula:
    """Bind symbolic time-path literals to their renamed arithmetic formula."""
    constraints = []
    for (depth, variable), formula in path.items():
        bound = depth2bound(depth)
        is_vertex = depth % 2 == 0
        renamed, _ = rename(formula, bound, is_vertex)
        if not is_vertex:
            renamed, _ = rename(formula, bound, False)
        constraints.append(Eq(_tracked_variable(variable), renamed))
    return And(constraints)


def contradiction_gen(clause_set: Set[Formula],
                      sub_formulas: Set[Formula]):
    """Link learned chi clauses to vertex and edge model propositions."""
    edge_constraints = []
    vertex_constraints = []
    for clause in clause_set:
        if not isinstance(clause, Bool) or "chi" not in clause.id:
            continue
        formula, _, depth = v_type1_info(clause.id, sub_formulas)
        if not is_proposition(formula):
            continue
        bound = depth2bound(depth)
        if depth % 2 == 1:
            renamed, _ = rename(formula, bound, is_vertex=False)
            edge_constraints.append(Eq(clause, renamed))
        else:
            vertex, _ = rename(formula, bound, is_vertex=True)
            edge, _ = rename(formula, bound + 1, is_vertex=False)
            vertex_constraints.append(Eq(clause, And([vertex, edge])))
    return And(vertex_constraints), And(edge_constraints)


def contradiction_gen_inv(boolean_dict: Dict[Bool, Formula]) -> Formula:
    constraints = []
    for variable, definition in boolean_dict.items():
        if "invAtomicID" not in variable.id:
            continue
        if not isinstance(definition, Forall):
            raise TypeError("invariant abstraction must be a Forall formula")
        constraints.append(Eq(variable, definition.const))
    return And(constraints)


__all__ = [
    "contradiction_gen", "contradiction_gen_inv", "is_mode_variable",
    "path2const", "time_path2const",
]

