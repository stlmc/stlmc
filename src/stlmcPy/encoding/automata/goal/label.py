from typing import Set, List

from ....constraints.constraints import *
from ....util.printer import indented_str


class Label:
    def __init__(self, st_cur: Set[Formula], tr_cur: Set[Formula],
                 st_nxt: Set[Formula], tr_nxt: Set[Formula]):
        # 0: state, 1: transition
        self._cur: List[Set[Formula]] = [st_cur, tr_cur]
        self._nxt: List[Set[Formula]] = [st_nxt, tr_nxt]

    @property
    def cur(self) -> Set[Formula]:
        return self._cur[0].union(self._cur[1])

    @property
    def nxt(self) -> Set[Formula]:
        return self._nxt[0].union(self._nxt[1])

    @property
    def state_cur(self) -> Set[Formula]:
        return self._cur[0].copy()

    @property
    def state_nxt(self) -> Set[Formula]:
        return self._nxt[0].copy()

    @property
    def transition_cur(self) -> Set[Formula]:
        return self._cur[1].copy()

    @property
    def transition_nxt(self) -> Set[Formula]:
        return self._nxt[1].copy()

    def __hash__(self):
        return hash((frozenset(self.cur), frozenset(self.nxt)))

    def __eq__(self, other):
        return self.__hash__() == hash(other)

    def __repr__(self):
        s, e = "Label (", ")"
        s_c = indented_str("cur:\n{}".format("\n".join([indented_str(str(c), 6) for c in self._cur[0]])), 4)
        s_n = indented_str("nxt:\n{}".format("\n".join([indented_str(str(n), 6) for n in self._nxt[0]])), 4)
        st = indented_str("state\n{}".format("\n".join([s_c, s_n])), 2)
        r_c = indented_str("cur:\n{}".format("\n".join([indented_str(str(c), 6) for c in self._cur[1]])), 4)
        r_n = indented_str("nxt:\n{}".format("\n".join([indented_str(str(n), 6) for n in self._nxt[1]])), 4)
        tr = indented_str("transition\n{}".format("\n".join([r_c, r_n])), 2)
        return "\n".join([s, st, tr, e])


class TypeVariable:
    def __init__(self, name: str):
        self._clk_id = name
        self._name = "type@{}".format(name)

    def get_clock(self):
        return Real(self._clk_id)

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return self._name


class OCProposition(Proposition):
    def __init__(self, v: TypeVariable, name: str):
        super().__init__()
        self.var = v
        self._name = name

    def get_clock(self):
        return self.var.get_clock()

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return self._name


class Open(OCProposition):
    def __init__(self, v: TypeVariable):
        super().__init__(v, "{} = open".format(v))


class Close(OCProposition):
    def __init__(self, v: TypeVariable):
        super().__init__(v, "{} = close".format(v))


class OpenClose(OCProposition):
    def __init__(self, v: TypeVariable):
        super().__init__(v, "{} = open || {} = close".format(v, v))


class ClkAssn(Proposition):
    def __init__(self, clock: Real, value: RealVal):
        super().__init__()
        self.clock, self.value = clock, value
        self._name = "{} := {}".format(clock, value)

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return self._name


class ClkReset(ClkAssn):
    def __init__(self, clock: Real):
        super().__init__(clock, RealVal("0.0"))


class Up(Formula):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval, formula: Formula, temporal: str):
        super().__init__()
        self.interval, self.temporal = interval, temporal
        self.formula, self.clock, self.type = formula, clk, ty
        self._name = "(up{}^{{{},{}}}_{} {})".format(temporal, clk, self.type, hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "(up{}^{{{},{}}}_{} {})".format(self.temporal, self.clock, self.type, self.interval, self.formula)


class UpDown(Formula):
    def __init__(self, clk1: Real, clk2: Real, ty1: TypeVariable, ty2: TypeVariable,
                 interval: Interval, formula: Formula, temporal1: str, temporal2: str):
        super().__init__()
        self.formula, self.interval = formula, interval
        self.temporal1, self.temporal2 = temporal1, temporal2
        self.clock, self.type = [clk1, clk2], [ty1, ty2]
        # hash
        self._up = "up{}^{{{},{}}}".format(temporal1, clk1, ty1)
        self._down = "down{}^{{{},{}}}".format(temporal2, clk2, ty2)
        self._name = "({} {})_{} {}".format(self._up, self._down, hash(interval), hash(formula))

    def __hash__(self):
        return hash(self._name)

    def __repr__(self):
        return "({} {})_{} {}".format(self._up, self._down, self.interval, self.formula)


class GloballyUp(Up):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval, formula: Formula):
        super().__init__(clk, ty, interval, formula, "[]")


class GloballyUpIntersect(Up):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval, formula: Formula):
        super().__init__(clk, ty, interval, formula, "[*]")


class GloballyUpDown(UpDown):
    def __init__(self, clk1: Real, clk2: Real, ty1: TypeVariable, ty2: TypeVariable,
                 interval: Interval, formula: Formula):
        super().__init__(clk1, clk2, ty1, ty2, interval, formula, "[]", "[]")


class GloballyUpIntersectDown(UpDown):
    def __init__(self, clk1: Real, clk2: Real, ty1: TypeVariable, ty2: TypeVariable,
                 interval: Interval, formula: Formula):
        super().__init__(clk1, clk2, ty1, ty2, interval, formula, "[*]", "[]")


class FinallyUp(Up):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval, formula: Formula):
        super().__init__(clk, ty, interval, formula, "<>")


class FinallyUpIntersect(Up):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval, formula: Formula):
        super().__init__(clk, ty, interval, formula, "<*>")


class FinallyUpDown(UpDown):
    def __init__(self, clk1: Real, clk2: Real, ty1: TypeVariable, ty2: TypeVariable,
                 interval: Interval, formula: Formula):
        super().__init__(clk1, clk2, ty1, ty2, interval, formula, "<>", "<>")


class FinallyUpIntersectDown(UpDown):
    def __init__(self, clk1: Real, clk2: Real, ty1: TypeVariable, ty2: TypeVariable,
                 interval: Interval, formula: Formula):
        super().__init__(clk1, clk2, ty1, ty2, interval, formula, "<*>", "<>")


class TimeProposition(Proposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval, temporal: str, name: str):
        Proposition.__init__(self)
        self.clock, self.ty, self.interval = clk, ty, interval
        self.temporal, self.name_s = temporal, name
        self._name = "T_{{{},{},{}}}^{{{},{}}}".format(temporal, hash(interval), name, clk, ty)

    def __repr__(self):
        return "T_{{{},{},{}}}^{{{},{}}}".format(self.temporal, self.interval,
                                                 self.name_s, self.clock, self.ty)

    def __hash__(self):
        return hash(self._name)

    def __eq__(self, other):
        return hash(self) == hash(other)


class TimeBound(Proposition):
    def __init__(self):
        super().__init__()

    def __repr__(self):
        return "tb"

    def __hash__(self):
        return hash("tb_f")


class TimeGloballyPre(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "[]", "pre")


class TimeGloballyFinal(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "[]", "final")


class TimeFinallyPre(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "<>", "pre")


class TimeFinallyFinal(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "<>", "final")


class TimeFinallyRestart(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "<>", "restart")
