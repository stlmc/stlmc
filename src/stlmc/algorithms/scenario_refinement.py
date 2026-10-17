"""Solver-independent helpers for two-step scenario refinement."""

from typing import Dict, List, Set

from ..constraints.constraints import (
    And, Bool, BoolVal, Eq, Formula, Not, Variable,
)
from ..constraints.analysis import get_vars
from ..constraints.substitution import substitution
from ..solver.abstract_solver import SolverStatus


def scenario_enumeration_finished(status: SolverStatus) -> bool:
    """Return whether an incremental abstraction query can make no progress."""
    return status in (SolverStatus.UNSAT, SolverStatus.UNKNOWN)


def is_temporal_auxiliary(variable: Variable) -> bool:
    """Identify private temporal/partition helpers, not model abstractions."""
    return isinstance(variable, Bool) and variable.id.startswith(
        ("rho^", "parU^", "parEnd")
    )


def assert_and_track_assignment(solver, formula: Formula, valuation: BoolVal,
                                track_id: str) -> Eq:
    """Track the exact polarity of a scenario literal and return that literal."""
    literal = Eq(formula, valuation)
    solver.track(literal, track_id)
    return literal


def evaluated_arithmetic_literals(clauses: Set[Formula],
                                   real_set: Set[Variable], model) -> List[Eq]:
    """Return exact truth assignments for clauses determined by real variables."""
    literals = []
    for clause_formula in clauses:
        if get_vars(clause_formula).intersection(real_set):
            literals.append(Eq(clause_formula, model.eval(clause_formula)))
    return literals


def relevant_boolean_abstract_links(boolean_abstract: Dict[Bool, Formula],
                                    roots: Formula,
                                    assignments=None) -> Formula:
    """Keep the dependency closure of abstraction definitions used by roots."""
    abstract_variables = set(boolean_abstract)
    pending = list(get_vars(roots).intersection(abstract_variables))
    relevant = set(pending)
    while pending:
        variable = pending.pop()
        dependencies = get_vars(boolean_abstract[variable]).intersection(
            abstract_variables
        )
        for dependency in dependencies.difference(relevant):
            relevant.add(dependency)
            pending.append(dependency)

    assignments = assignments or {}
    links = []
    for variable in boolean_abstract:
        if variable not in relevant:
            continue
        definition = substitution(boolean_abstract[variable], assignments)
        if variable in assignments:
            links.append(
                definition
                if assignments[variable] == BoolVal("True")
                else Not(definition)
            )
        else:
            links.append(Eq(variable, definition))
    return And(links)


def boolean_core_assignments(formula: Formula) -> Dict[Bool, BoolVal]:
    """Collect explicit Boolean equalities retained in a scenario core."""
    assignments = {}
    pending = [formula]
    while pending:
        current = pending.pop()
        if isinstance(current, And):
            pending.extend(current.children)
            continue
        if not isinstance(current, Eq):
            continue
        if isinstance(current.left, Bool) and isinstance(current.right, BoolVal):
            assignments[current.left] = current.right
        elif isinstance(current.right, Bool) and isinstance(current.left, BoolVal):
            assignments[current.right] = current.left
    return assignments


__all__ = [
    "is_temporal_auxiliary",
    "assert_and_track_assignment",
    "boolean_core_assignments",
    "evaluated_arithmetic_literals",
    "relevant_boolean_abstract_links",
    "scenario_enumeration_finished",
]
