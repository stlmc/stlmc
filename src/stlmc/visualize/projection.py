"""Projection of solver assignments into ordered visualization inputs."""

from typing import Dict, List, Set

from ..constraints.constraints import Constraint, Variable


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
            int(float(self.assignment[variable].value))
            for variable in self.get_ordered_mode_vars()
        ]
        return [self.modules[module_id] for module_id in module_ids]


__all__ = ["Projector"]
