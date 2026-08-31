"""Validation and classification of user-defined plot groups."""

from typing import List, Set


def split_groups(groups: List[Set[str]], state_vars: Set[str],
                 robust_vars: Set[str]):
    state_groups = []
    robust_groups = []
    # Preserve the historical stack order used by the CLI/visualizer.
    for group in reversed(groups):
        if group.issubset(state_vars):
            state_groups.append(group)
        elif group.issubset(robust_vars):
            robust_groups.append(group)
        else:
            raise ValueError("group contains wrong variables : {}".format(group))
    return state_groups, robust_groups


def pairwise_disjoint_check(groups: List[Set[str]]):
    for index, group in enumerate(groups):
        for other in groups[index + 1:]:
            intersection = group.intersection(other)
            if intersection:
                raise ValueError(
                    "state variables {} belong to multiple groups".format(
                        intersection
                    )
                )


def flatten(groups: List[Set[str]]) -> Set[str]:
    return set().union(*groups) if groups else set()


__all__ = ["flatten", "pairwise_disjoint_check", "split_groups"]
