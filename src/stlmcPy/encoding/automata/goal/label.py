from typing import Set

from .interval import SymbolicInterval, Partition
from ....constraints.constraints import *
from ....util.printer import indented_str


class Label:
    def __init__(self, cur: Set[Formula], nxt: Set[Formula],
                 forbidden: Set[Formula], assertion: Set[Formula]):
        self.cur, self.nxt, self.forbidden, self.assertion = cur, nxt, forbidden, assertion

    def __hash__(self):
        return hash((frozenset(self.cur), frozenset(self.nxt), frozenset(self.forbidden), frozenset(self.assertion)))

    def __eq__(self, other):
        return self.__hash__() == hash(other)

    def __repr__(self):
        s, e = "Label (", ")"
        c = indented_str("cur:\n{}".format("\n".join([indented_str(str(c), 4) for c in self.cur])), 2)
        n = indented_str("nxt:\n{}".format("\n".join([indented_str(str(n), 4) for n in self.nxt])), 2)
        f = indented_str("forbidden:\n{}".format("\n".join([indented_str(str(fb), 4) for fb in self.forbidden])), 2)
        a = indented_str("assertions:\n{}".format("\n".join([indented_str(str(ast), 4) for ast in self.assertion])), 2)
        return "\n".join([s, c, n, f, a, e])


class Up(UnaryFormula):
    def __init__(self, i: SymbolicInterval, interval: Interval, formula: Formula, temporal: str):
        super().__init__(formula, "", "")
        self.i, self.interval, self._temporal = i, interval, temporal
        self._name = "(up{}^{}_{} {})".format(temporal, hash(i), hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "(up{}^{}_{} {})".format(self._temporal, self.i, self.interval, self.child)


class UpIntersect(UnaryFormula):
    def __init__(self, i: SymbolicInterval, interval: Interval, formula: Formula, temporal: str):
        super().__init__(formula, "", "")
        self.i, self.interval, self._temporal = i, interval, temporal
        self._name = "(up{}^{}_{} {})".format(temporal, hash(i), hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "(up{}^{}_{} {})".format(self._temporal, self.i, self.interval, self.child)


class UpDown(UnaryFormula):
    def __init__(self, i: SymbolicInterval, k: SymbolicInterval,
                 interval: Interval, formula: Formula, temporal):
        super().__init__(formula, "", "")
        self._temporal, self.i, self.k, self.interval = temporal, i, k, interval
        self._name = "((up&down{}^{{{}, {}}})_{} {})".format(temporal, hash(i), hash(k),
                                                             hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "(up&down{}^{{{}, {}}})_{} {})".format(self._temporal, self.i, self.k, self.interval, self.child)


class UpIntersectDown(UnaryFormula):
    def __init__(self, i: SymbolicInterval, k: SymbolicInterval,
                 interval: Interval, formula: Formula, temporal1: str, temporal2: str):
        super().__init__(formula, "", "")
        self.i, self.k, self.interval = i, k, interval
        self._temporal1, self._temporal2 = temporal1, temporal2
        self._name = "((up{}&down{})^{{{}, {}}}_{} {})".format(temporal1, temporal2, hash(i), hash(k),
                                                               hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "((up{}&down{})^{{{}, {}}}_{} {})".format(self._temporal1, self._temporal2,
                                                         self.i, self.k, self.interval, self.child)


class GloballyUp(Up):
    def __init__(self, i: SymbolicInterval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "[]")


class GloballyUpIntersect(UpIntersect):
    def __init__(self, i: SymbolicInterval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "[*]")


class GloballyUpDown(UpDown):
    def __init__(self, i: SymbolicInterval, k: SymbolicInterval,
                 interval: Interval, formula: Formula):
        super().__init__(i, k, interval, formula, "[]")


class GloballyUpIntersectDown(UpIntersectDown):
    def __init__(self, i: SymbolicInterval, k: SymbolicInterval,
                 interval: Interval, formula: Formula):
        super().__init__(i, k, interval, formula, "[*]", "[]")


class FinallyUp(Up):
    def __init__(self, i: SymbolicInterval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "<>")


class FinallyUpIntersect(UpIntersect):
    def __init__(self, i: SymbolicInterval, interval: Interval, formula: Formula):
        super().__init__(i, interval, formula, "<*>")


class FinallyUpDown(UpDown):
    def __init__(self, i: SymbolicInterval, k: SymbolicInterval,
                 interval: Interval, formula: Formula):
        super().__init__(i, k, interval, formula, "<>")


class FinallyUpIntersectDown(UpIntersectDown):
    def __init__(self, i: SymbolicInterval, k: SymbolicInterval,
                 interval: Interval, formula: Formula):
        super().__init__(i, k, interval, formula, "<*>", "<>")


class TimeProposition(Proposition):
    def __init__(self, i: SymbolicInterval, interval: Interval, name: str):
        Proposition.__init__(self)
        self.i, self.interval, self._name = i, interval, name

    def __repr__(self):
        return self._name

    def __hash__(self):
        return hash(self._name)

    def __eq__(self, other):
        return hash(self) == hash(other)


class TimeIntersect(TimeProposition):
    def __init__(self, i: SymbolicInterval, interval: Interval):
        TimeProposition.__init__(self, i, interval, "(K /\\ {} + {} != empty)_in".format(i, interval))


class TimePre(TimeProposition):
    def __init__(self, i: SymbolicInterval, interval: Interval):
        TimeProposition.__init__(self, i, interval, "(K < {} + {})_pre".format(i, interval))


class TimePost(TimeProposition):
    def __init__(self, i: SymbolicInterval, interval: Interval):
        TimeProposition.__init__(self, i, interval, "({} + {} <! K)_post".format(i, interval))


class TimeNotPost(TimeProposition):
    def __init__(self, i: SymbolicInterval, interval: Interval):
        TimeProposition.__init__(self, i, interval, "(K <! {} + {})_!post".format(i, interval))


class TimeLast(TimeProposition):
    def __init__(self):
        dummy, glb_itv = Partition(-1), Interval(True, "tau_0", "tau_max", False)
        TimeProposition.__init__(self, dummy, glb_itv, "(K >= tau_max)_last")


class TimePreFinally(TimeProposition):
    def __init__(self, i: SymbolicInterval, interval: Interval):
        TimeProposition.__init__(self, i, interval, "(rc({}) issubset_of rc(K - {}))_<>pre".format(i, interval))


class TimeIntersectFinally(TimeProposition):
    def __init__(self, i: SymbolicInterval, interval: Interval):
        TimeProposition.__init__(self, i, interval, "(inf({}) in K - {})_<>in".format(i, interval))


class TimePostFinally(TimeProposition):
    def __init__(self, i: SymbolicInterval, interval: Interval):
        TimeProposition.__init__(self, i, interval, "(sup({}) in K - I)_<>post".format(i, interval))
