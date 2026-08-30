from typing import List, Tuple

from ..constraints.constraints import And, Formula, Or
from ..exceptions import IllegalArgumentError


Candidate = Tuple[Formula, Formula]


def _same_formula(left: Formula, right: Formula) -> bool:
    # Constraint.__eq__ constructs an Eq formula, so it cannot be used as a
    # Python structural-equality predicate.
    return hash(left) == hash(right) and repr(left) == repr(right)


def candidate_batch_formula(candidates: List[Candidate]) -> Formula:
    """Combine final solver candidates, factoring an identical common part."""
    if len(candidates) == 0:
        raise IllegalArgumentError("candidate batch cannot be empty")

    common = candidates[0][0]
    if all(_same_formula(candidate_common, common)
           for candidate_common, _ in candidates):
        candidate_parts = [candidate_part for _, candidate_part in candidates]
        disjunction = (
            candidate_parts[0]
            if len(candidate_parts) == 1
            else Or(candidate_parts)
        )
        return And([common, disjunction])

    return Or([
        And([candidate_common, candidate_part])
        for candidate_common, candidate_part in candidates
    ])
