from typing import Tuple, Set, FrozenSet

from ....constraints.constraints import *

# Label = Tuple[FrozenSet[Formula], FrozenSet[Formula], FrozenSet[Formula]]
from ....util.printer import indented_str


class Label:
    def __init__(self, cur: Set[Formula], nxt: Set[Formula], forbidden: Set[Formula]):
        self.cur, self.nxt, self.forbidden = cur, nxt, forbidden

    def __hash__(self):
        return hash((frozenset(self.cur), frozenset(self.nxt), frozenset(self.forbidden)))

    def __eq__(self, other):
        return self.__hash__() == hash(other)

    def __repr__(self):
        s, e = "Label (", ")"
        c = indented_str("cur:\n{}".format("\n".join([indented_str(str(c), 4) for c in self.cur])), 2)
        n = indented_str("nxt:\n{}".format("\n".join([indented_str(str(n), 4) for n in self.nxt])), 2)
        f = indented_str("forbidden:\n{}".format("\n".join([indented_str(str(fb), 4) for fb in self.forbidden])), 2)
        return "\n".join([s, c, n, f, e])


class Up(UnaryFormula):
    def __init__(self, i: Interval, interval: Interval, formula: Formula, temporal: str):
        super().__init__(formula, "", "")
        self.i, self.interval, self._temporal = i, interval, temporal
        self._name = "(up{}^{}_{} {})".format(temporal, hash(i), hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "{} (J:{}, I:{} {})".format(self._name, self.i, self.interval, self.child)


class Down(UnaryFormula):
    def __init__(self, i: Interval, interval: Interval, formula: Formula, temporal: str):
        super().__init__(formula, "", "")
        self.i, self.interval, self._temporal = i, interval, temporal
        self._name = "(down{}^{}_{} {})".format(temporal, hash(i), hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "{} (J:{}, I:{}, {})".format(self._name, self.i, self.interval, self.child)


class UpDown(UnaryFormula):
    def __init__(self, i: Interval, k: Interval, interval: Interval, formula: Formula, temporal):
        super().__init__(formula, "", "")
        self._temporal, self.i, self.k, self.interval = temporal, i, k, interval
        self._name = "((up&down{}^{{{}, {}}})_{} {})".format(temporal, hash(i), hash(k),
                                                             hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "{} (J:{}, K:{}, I:{}, {})".format(self._name, self.i, self.k, self.interval, self.child)


class UpIntersectionDown(UnaryFormula):
    def __init__(self, i: Interval, interval: Interval, formula: Formula, temporal1: str, temporal2: str):
        super().__init__(formula, "", "")
        self.i, self.interval = i, interval
        self._temporal1, self._temporal2 = temporal1, temporal2
        self._name = "((up{}&down{})^{}_{} {})".format(temporal1, temporal2, hash(i),
                                                       hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "{} (J:{}, I:{}, {})".format(self._name, self.i, self.interval, self.child)


class GloballyUp(Up):
    def __init__(self, i: Interval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "[]")


class GloballyUpIntersect(Up):
    def __init__(self, i: Interval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "[*]")


class GloballyDown(Down):
    def __init__(self, i: Interval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "[]")


class GloballyUpDown(UpDown):
    def __init__(self, i: Interval, k: Interval, interval: Interval, formula: Formula):
        super().__init__(i, k, interval, formula, "[]")


class GloballyUpIntersectDown(UpIntersectionDown):
    def __init__(self, i: Interval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "[*]", "[]")


class FinallyUp(Up):
    def __init__(self, i: Interval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "<>")


class FinallyUpIntersect(Up):
    def __init__(self, i: Interval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "<*>")


class FinallyDown(Down):
    def __init__(self, i: Interval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "<>")


class FinallyUpDown(UpDown):
    def __init__(self, i: Interval, k: Interval, interval: Interval, formula: Formula):
        super().__init__(i, k, interval, formula, "<>")


class FinallyUpIntersectDown(UpIntersectionDown):
    def __init__(self, i: Interval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "<*>", "<>")


class TimeProposition(Proposition):
    def __init__(self, i: Interval, k: Interval, interval: Interval, name: str):
        Proposition.__init__(self)
        self.i, self.k, self.interval, self._name = i, k, interval, name

    def __repr__(self):
        return self._name

    def __hash__(self):
        return hash(self._name)

    def __eq__(self, other):
        return hash(self) == hash(other)


class TimeIntersect(TimeProposition):
    def __init__(self, i: Interval, k: Interval, interval: Interval):
        TimeProposition.__init__(self, i, k, interval, "({} /\\ {} + {} != empty)_in".format(k, i, interval))


class TimePre(TimeProposition):
    def __init__(self, i: Interval, k: Interval, interval: Interval):
        TimeProposition.__init__(self, i, k, interval, "({} < {} + {})_pre".format(k, i, interval))


class TimePost(TimeProposition):
    def __init__(self, i: Interval, k: Interval, interval: Interval):
        TimeProposition.__init__(self, i, k, interval, "({} + {} <! {})_post".format(i, interval, k))


class TimeNotPost(TimeProposition):
    def __init__(self, i: Interval, k: Interval, interval: Interval):
        TimeProposition.__init__(self, i, k, interval, "({} <! {} + {})_!post".format(k, i, interval))


class TimeLast(TimeProposition):
    def __init__(self, i: Interval):
        TimeProposition.__init__(self, i, i, Interval(True, "tau_0", "tau_max", False),
                                 "({} >= tau_max)_last".format(i))
