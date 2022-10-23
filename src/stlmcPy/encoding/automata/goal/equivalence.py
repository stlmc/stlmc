import abc
from functools import singledispatch, singledispatchmethod
from itertools import product
from typing import List

from .interval import equal, type_equivalent
from .label import *


class LabelEquivalenceChecker:
    def __init__(self):
        self._filters = {
            "up[]": lambda x: isinstance(x, GloballyUp),
            "up[*]": lambda x: isinstance(x, GloballyUpIntersect),
            "up<>": lambda x: isinstance(x, FinallyUp),
            "up<*>": lambda x: isinstance(x, FinallyUpIntersect),

            "up&down[]": lambda x: isinstance(x, GloballyUpDown),
            "up[*]down[]": lambda x: isinstance(x, GloballyUpIntersectDown),
            "up&down<>": lambda x: isinstance(x, FinallyUpDown),
            "up<*>down<>": lambda x: isinstance(x, FinallyUpIntersectDown)
        }

    @abc.abstractmethod
    def equivalent(self, label1: Label, label2: Label) -> bool:
        pass

    def _apply_filter(self, formulas: Set[Formula], *names) -> List[Set[Formula]]:
        if len(names) <= 0:
            return [formulas]

        categories = list()
        for name in names:
            assert name in self._filters
            categories.append(set(filter(self._filters[name], formulas)))
        return categories


class StutteringEquivalenceChecker(LabelEquivalenceChecker):
    def __init__(self):
        LabelEquivalenceChecker.__init__(self)
        self._filters["non-time"] = lambda x: not isinstance(x, TimeProposition)

    def equivalent(self, label1: Label, label2: Label) -> bool:
        # get non-time goals
        c1 = self._apply_filter(label1.cur, "non-time").pop()
        c2 = self._apply_filter(label2.cur, "non-time").pop()

        c1_cg = self._apply_filter(c1, "up[]", "up[*]", "up<>", "up<*>")
        c2_cg = self._apply_filter(c2, "up&down[]", "up[*]down[]", "up&down<>", "up<*>down<>")

        pair = set()
        for c1_fs, c2_fs in zip(c1_cg, c2_cg):
            for f1, f2 in product(c1_fs, c2_fs):
                if self._stuttering_pair(f1, f2):
                    pair.add((f1, f2))

        c1_cpy, c2_cpy = c1.copy(), c2.copy()
        for f1, f2 in pair:
            c1_cpy.remove(f1)
            c2_cpy.remove(f2)

        return c1_cpy == c2_cpy

    @singledispatchmethod
    def _stuttering_pair(self, cur: Formula, nxt: Formula) -> bool:
        return False

    @_stuttering_pair.register(Up)
    def _(self, cur: Up, nxt: Formula) -> bool:
        if not isinstance(nxt, UpDown):
            return False

        partition_eq, interval_eq = equal(cur.i, nxt.i), cur.interval == nxt.interval
        f_eq = hash(cur.child) == hash(nxt.child)
        return partition_eq and interval_eq and f_eq

    @_stuttering_pair.register(UpIntersect)
    def _(self, cur: UpIntersect, nxt: Formula) -> bool:
        if not isinstance(nxt, UpIntersectDown):
            return False

        interval_eq = cur.interval == nxt.interval
        f_eq = hash(cur.child) == hash(nxt.child)
        return interval_eq and f_eq


class ShiftingEquivalenceChecker(LabelEquivalenceChecker):
    def __init__(self):
        LabelEquivalenceChecker.__init__(self)
        self._shifting = 0

    def equivalent(self, label1: Label, label2: Label) -> bool:
        self._clear()
        # get current
        c1, c2 = label1.cur.copy(), label2.cur.copy()

        # categorize
        c1_cg = self._apply_filter(c1, "up[]", "up[*]", "up<>", "up<*>",
                                   "up&down[]", "up[*]down[]", "up&down<>", "up<*>down<>")
        c2_cg = self._apply_filter(c2, "up[]", "up[*]", "up<>", "up<*>",
                                   "up&down[]", "up[*]down[]", "up&down<>", "up<*>down<>")

        pair = set()
        self._shifting = 0
        is_first = True
        for c1_fs, c2_fs in zip(c1_cg, c2_cg):
            for f1, f2 in product(c1_fs, c2_fs):
                if self._shifting_pair(f1, f2):
                    pair.add((f1, f2))
                    # no need to update shifting for UpIntersect
                    # really?
                    if is_up_intersect(f1, f2):
                        continue
                    else:
                        prev_shifting = self._shifting
                        self._shifting = _calc_shifting(f1, f2)
                        if is_first:
                            # do not check
                            is_first = False
                        else:
                            # conclude that the labels are not equivalent
                            if prev_shifting != self._shifting:
                                return False

        c1_cpy, c2_cpy = c1.copy(), c2.copy()
        for f1, f2 in pair:
            c1_cpy.remove(f1)
            c2_cpy.remove(f2)

        return c1_cpy == c2_cpy

    def get_shifting(self):
        return self._shifting

    def _clear(self):
        self._shifting = 0

    @singledispatchmethod
    def _shifting_pair(self, cur: Formula, nxt: Formula) -> bool:
        return False

    @_shifting_pair.register(Up)
    def _(self, cur: Up, nxt: Up):
        assert isinstance(nxt, Up)
        partition_eq = type_equivalent(cur.i, nxt.i)
        interval_eq, f_eq = cur.interval == nxt.interval, hash(cur.child) == hash(nxt.child)
        return partition_eq and interval_eq and f_eq

    @_shifting_pair.register(UpIntersect)
    def _(self, cur: UpIntersect, nxt: UpIntersect):
        assert isinstance(nxt, UpIntersect)
        interval_eq = cur.interval == nxt.interval
        f_eq = hash(cur.child) == hash(nxt.child)
        return interval_eq and f_eq

    @_shifting_pair.register(UpDown)
    def _(self, cur: UpDown, nxt: UpDown):
        assert isinstance(nxt, UpDown)
        partition_eqs = all([type_equivalent(cur.i, nxt.i), type_equivalent(cur.k, nxt.k)])
        shifting_eq = cur.k.index - cur.i.index == nxt.k.index - nxt.i.index
        interval_eq, f_eq = cur.interval == nxt.interval, hash(cur.child) == hash(nxt.child)
        return partition_eqs and shifting_eq and interval_eq and f_eq

    @_shifting_pair.register(UpIntersectDown)
    def _(self, cur: UpIntersectDown, nxt: UpIntersectDown):
        assert isinstance(nxt, UpIntersectDown)
        partition_eq = type_equivalent(cur.i, nxt.i)
        interval_eq, f_eq = cur.interval == nxt.interval, hash(cur.child) == hash(nxt.child)
        return partition_eq and interval_eq and f_eq


def is_up_intersect(cur: UpIntersect, nxt: UpIntersect):
    return isinstance(cur, UpIntersect) and isinstance(nxt, UpIntersect)


@singledispatch
def _calc_shifting(cur: Formula, nxt: Formula) -> int:
    raise Exception("cannot calculate shifting of {} and {}".format(cur, nxt))


@_calc_shifting.register(Up)
def _(cur: Up, nxt: Up):
    assert isinstance(nxt, Up)
    return nxt.i.index - cur.i.index


@_calc_shifting.register(UpDown)
def _(cur: UpDown, nxt: UpDown):
    assert isinstance(nxt, UpDown)
    # assert cur.k.index - cur.i.index == nxt.k.index - nxt.i.index
    return nxt.i.index - cur.i.index


@_calc_shifting.register(UpIntersectDown)
def _(cur: UpIntersectDown, nxt: UpIntersectDown):
    assert isinstance(nxt, UpIntersectDown)
    return nxt.i.index - cur.i.index
