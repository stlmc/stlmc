"""Translate abstract scenario paths and cores into model constraints."""

from typing import Dict, Set, Tuple

from ..constraints.constraints import (
    And, Bool, BoolVal, Eq, Forall, Formula, Geq, Gt, Implies, Leq, Lt,
    Not, Or, Real, RealVal,
)
from ..constraints.logical_normalization import reduce_not
from ..constraints.analysis import get_vars
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
        renamed, _ = rename(formula, bound, is_vertex, model.mode_var_dict)
        tracked = _tracked_variable(variable)

        if not is_vertex:
            renamed_edge, _ = rename(formula, bound, False, model.mode_var_dict)
            constraints.append(Eq(tracked, renamed_edge))
            continue
        if is_mode_variable(variable, model):
            renamed_edge, _ = rename(formula, bound, False, model.mode_var_dict)
            constraints.append(Eq(tracked, renamed_edge))
            continue

        # Numeric mode variables are constant over a continuous segment,
        # just like Boolean modes. Never create phantom continuous endpoints
        # for them or pass a mode-only predicate to native ODE quantifiers.
        if all(is_mode_variable(v, model) for v in get_vars(formula)):
            constraints.append(Or([
                Eq(symbolic_sup(depth), symbolic_inf(depth)),
                Eq(tracked, renamed),
            ]))
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


def _endpoint_closure(predicate: Formula) -> Formula:
    """A necessary endpoint condition for a continuous interval predicate."""
    if isinstance(predicate, Gt):
        return Geq(predicate.left, predicate.right)
    if isinstance(predicate, Lt):
        return Leq(predicate.left, predicate.right)
    if isinstance(predicate, (Geq, Leq, Eq)):
        if not isinstance(predicate.left, Bool):
            return predicate
    # In particular, disequality need not hold at an excluded endpoint.
    return BoolVal("True")


def contradiction_gen(clause_set: Set[Formula],
                      sub_formulas: Set[Formula], model=None):
    """Link learned chi clauses to vertex and edge model propositions."""
    edge_constraints = []
    vertex_constraints = []
    mode_variables = model.mode_var_dict if model is not None else {}
    for clause in clause_set:
        if not isinstance(clause, Bool) or "chi" not in clause.id:
            continue
        formula, _, depth = v_type1_info(clause.id, sub_formulas)
        if not is_proposition(formula):
            continue
        bound = depth2bound(depth)
        if depth % 2 == 1:
            renamed, _ = rename(formula, bound, is_vertex=False,
                                mode_variables=mode_variables)
            edge_constraints.append(Eq(clause, renamed))
        else:
            # A flow proposition describes an OPEN interval. Equality to
            # strict endpoint predicates would exclude valid threshold
            # crossings at partition endpoints. Only use necessary closure
            # conditions, and infer nothing from an empty interval.
            conditions = []
            for polarity, predicate in (
                    (clause, formula), (Not(clause), reduce_not(Not(formula)))):
                closed = _endpoint_closure(predicate)
                vertex, _ = rename(closed, bound, is_vertex=True,
                                   mode_variables=mode_variables)
                edge, _ = rename(closed, bound + 1, is_vertex=False,
                                 mode_variables=mode_variables, mode_bound=bound)
                conditions.append(Implies(polarity, And([vertex, edge])))
            vertex_constraints.append(Implies(
                symbolic_inf(depth) < symbolic_sup(depth), And(conditions),
            ))
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

