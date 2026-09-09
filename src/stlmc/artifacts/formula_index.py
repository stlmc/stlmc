from typing import Dict, Set, Tuple

from ..constraints.constraints import (
    BinaryFormula, Formula, Implies, MultinaryFormula, Not, UnaryFormula,
)
from ..constraints.analysis import is_proposition


def index_subformulas(formula: Formula) -> Tuple[Set[Formula], Dict]:
    """Assign stable-in-run display indices without visualization imports."""
    if not isinstance(formula, Formula):
        raise TypeError("expected a formula")

    formula_ids = {}
    formulas = {formula}
    pending = [(0, formula)]
    next_id = 1
    while pending:
        formula_id, current = pending.pop()
        if current in formula_ids:
            continue
        formula_ids[current] = formula_id
        if is_proposition(current):
            continue
        if isinstance(current, UnaryFormula):
            children = [current.child]
        elif isinstance(current, BinaryFormula):
            children = (
                [Not(current.left), current.right]
                if isinstance(current, Implies)
                else [current.left, current.right]
            )
        elif isinstance(current, MultinaryFormula):
            children = list(current.children)
        else:
            del formula_ids[current]
            formulas.discard(current)
            continue
        for child in children:
            formulas.add(child)
            pending.append((next_id, child))
            next_id += 1
    return formulas, formula_ids


# Historical public name used by visualization configurations.
sub_formula = index_subformulas
