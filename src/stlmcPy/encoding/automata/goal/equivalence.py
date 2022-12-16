from itertools import permutations
from typing import Tuple

from .clock import filter_clock_goals, get_clock_pool, make_clk_type_mapping, ClockSubstitution
from .label import *


class StutteringEquivalenceChecker:
    def __init__(self, top_formula: Formula):
        self._formula = top_formula

    def equivalent(self, label1: Label, label2: Label) -> bool:
        # ignore transitions
        cond = [self._equivalent(label1.state_cur, label2.state_cur),
                self._equivalent(label1.state_nxt, label2.state_nxt)]
        return all(cond)

    def _equivalent(self, goal1: Set[Formula], goal2: Set[Formula]) -> bool:
        # ignore top formula
        n_goals = [self._ignore_top_formula(*goal1),
                   self._ignore_top_formula(*goal2)]

        # split clock and others
        n_clk_s = [filter_clock_goals(*n_goals[0]),
                   filter_clock_goals(*n_goals[1])]

        n_other = [n_goals[0].difference(n_clk_s[0]),
                   n_goals[1].difference(n_clk_s[1])]

        clk_eq = self._clock_eq(n_clk_s[0], n_clk_s[1])

        if clk_eq and n_other[0] == n_other[1]:
            return True
        return False

    @classmethod
    def _clock_eq(cls, goal1: Set[Formula], goal2: Set[Formula]) -> bool:
        # clock equivalence detection
        # 1) get clock pools of the goals
        # 1.1) if the pools' size differ, the goals are not equivalent
        p1, p2 = get_clock_pool(*goal1), get_clock_pool(*goal2)

        if len(p1) != len(p2):
            return False

        # 2) (assume that the pools are equal) make mappings
        # Dict[Real, Set[str]]
        clk_ty_map1 = make_clk_type_mapping(*goal1)

        # 3) check if the mappings are equal
        # fix ordering of p1 and calculate all possible orderings of p2
        p1_o, p2_o_pool = tuple(p1), set(permutations(p2))

        for p2_o in p2_o_pool:
            assert isinstance(p2_o, Tuple)

            # possible clock mapping
            possible = set(zip(p1_o, p2_o))
            mapping = ClockSubstitution()
            for c1, c2 in possible:
                mapping.add(c2, c1)

            goals = set(map(lambda x: mapping.substitute(x), goal2))
            clk_ty_map2 = make_clk_type_mapping(*goals)

            # find the same clock mapping
            if clk_ty_map1 == clk_ty_map2:
                return True

        # otherwise
        return False

    def _ignore_top_formula(self, *goals) -> Set[Formula]:
        return set(filter(lambda x: hash(x) != hash(self._formula), goals))
