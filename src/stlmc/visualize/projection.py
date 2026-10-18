"""Projection of solver assignments into ordered visualization inputs."""

from typing import Dict, List, Set

from ..constraints.constraints import Constraint, Real, Variable
from .numbers import number_float


def continuous_values(assignment: dict, continuous_variables: dict,
                      max_bound: int):
    """Project indexed endpoint assignments into per-bound value pairs."""
    result = {}
    for variable in continuous_variables:
        values = []
        for bound in range(max_bound + 1):
            initial = assignment[Real("{}_{}_0".format(variable.id, bound))]
            final = assignment[Real("{}_{}_t".format(variable.id, bound))]
            values.append((
                number_float(initial.value),
                number_float(final.value),
            ))
        result[variable.id] = values
    return result


class Projector:
    def __init__(self, assignment, mode_var_dict: Dict[str, Variable],
                 proposition_dict: Dict[Variable, Constraint], modules: Dict):
        self.assignment = assignment
        self.mode_var_dict = mode_var_dict
        self.proposition_dict = proposition_dict
        self.modules = modules

    def find_all_with_keywords(self, keyword: str) -> List[Variable]:
        return [variable for variable in self.assignment if keyword in variable.id]

    def get_variable_points(self) -> List[Variable]:
        return sorted(
            self.find_all_with_keywords("tau"),
            key=lambda variable: int(variable.id[4:]),
        )

    def get_mode_vars(self) -> Set[Variable]:
        return set(self.proposition_dict).union(self.mode_var_dict.values())

    def get_ordered_mode_vars(self) -> List[Variable]:
        prefix = "currentMode_"
        return sorted(
            self.find_all_with_keywords(prefix),
            key=lambda variable: int(variable.id[len(prefix):]),
        )

    def get_max_bound(self) -> int:
        ordered = self.get_ordered_mode_vars()
        if not ordered:
            raise ValueError("assignment has no currentMode variables")
        return int(ordered[-1].id[len("currentMode_"):])

    def get_ordered_modules(self) -> List[Dict]:
        module_ids = [
            int(number_float(self.assignment[variable].value))
            for variable in self.get_ordered_mode_vars()
        ]
        return [self.modules[module_id] for module_id in module_ids]


__all__ = ["Projector", "continuous_values"]
