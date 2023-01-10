from typing import Optional

from ....constraints.aux.operations import *
from ....util.printer import indented_str


class Label:
    def __init__(self, st_cur: Set[Formula], tr_cur: Set[Formula],
                 st_nxt: Set[Formula], tr_nxt: Set[Formula],
                 assertion: Set[Formula], forbidden: Set[Formula],
                 max_clock_index: int):
        # 0: state, 1: transition
        self._cur: List[Set[Formula]] = [st_cur, tr_cur]
        self._nxt: List[Set[Formula]] = [st_nxt, tr_nxt]
        self.assertion, self.forbidden = assertion, forbidden
        self._max_clock_index = max_clock_index

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

    @property
    def max_clock_index(self) -> int:
        return self._max_clock_index

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
        s_a = indented_str("assertion:\n{}".format("\n".join([indented_str(str(a), 6) for a in self.assertion])), 4)
        s_f = indented_str("forbidden:\n{}".format("\n".join([indented_str(str(a), 6) for a in self.forbidden])), 4)
        cc = indented_str("clock counter:\n{}".format(indented_str(str(self._max_clock_index), 6)), 4)
        tr = indented_str("transition\n{}".format("\n".join([r_c, r_n])), 2)
        return "\n".join([s, st, tr, s_a, s_f, cc, e])


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


class TimeFinal(Proposition):
    def __init__(self, interval: Interval, temporal: str):
        super().__init__()
        self.interval = interval
        self._name = "T_{{{},{}, final}}".format(temporal, hash(interval))

    def __repr__(self):
        return self._name

    def __hash__(self):
        return hash(self._name)


class TimeGloballyUpIntersectFinal(TimeFinal):
    def __init__(self, interval: Interval):
        TimeFinal.__init__(self, interval, "[*]")


class TimeFinallyUpIntersectFinal(TimeFinal):
    def __init__(self, interval: Interval):
        TimeFinal.__init__(self, interval, "<*>")


class TimeGloballyUpFinal(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "[]", "final")


class TimeGloballyPre(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "[]", "pre")


class TimeGloballyIn(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "[]", "in")


class TimeFinallyPre(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "<>", "pre")


class TimeFinallyIn(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "<>", "in")


class TimeFinallyUpFinal(TimeProposition):
    def __init__(self, clk: Real, ty: TypeVariable, interval: Interval):
        TimeProposition.__init__(self, clk, ty, interval, "<>", "final")


@singledispatch
def translate_time_goal(formula: Formula) -> Optional[Formula]:
    return None


@translate_time_goal.register(TimeGloballyPre)
def _(formula: TimeGloballyPre) -> Optional[Formula]:
    # ignore strict case
    return formula.clock <= inf(formula.interval)


@translate_time_goal.register(TimeGloballyIn)
def _(formula: TimeGloballyIn) -> Optional[Formula]:
    # ignore strict case
    return formula.clock >= inf(formula.interval)


@translate_time_goal.register(TimeGloballyUpIntersectFinal)
def _(formula: TimeGloballyUpIntersectFinal) -> Optional[Formula]:
    # ignore strict case
    return RealVal("0.0") >= sup(formula.interval)


@translate_time_goal.register(TimeGloballyUpFinal)
def _(formula: TimeGloballyUpFinal) -> Optional[Formula]:
    # ignore strict case
    return formula.clock >= sup(formula.interval)


@translate_time_goal.register(TimeFinallyPre)
def _(formula: TimeFinallyPre) -> Optional[Formula]:
    # ignore strict case
    return formula.clock <= sup(formula.interval)


@translate_time_goal.register(TimeFinallyIn)
def _(formula: TimeFinallyIn) -> Optional[Formula]:
    # ignore strict case
    return formula.clock >= inf(formula.interval)


@translate_time_goal.register(TimeFinallyUpIntersectFinal)
def _(formula: TimeFinallyUpIntersectFinal) -> Optional[Formula]:
    # ignore strict case
    return RealVal("0.0") >= inf(formula.interval)


@translate_time_goal.register(TimeFinallyUpFinal)
def _(formula: TimeFinallyUpFinal) -> Optional[Formula]:
    # ignore strict case
    return formula.clock >= inf(formula.interval)


@translate_time_goal.register(TimeBound)
def _(formula: TimeBound) -> Optional[Formula]:
    tb = global_clk() >= tau_max()
    assert isinstance(tb, Formula)
    return tb


def tau_max():
    return Real("tau_max")


def global_clk():
    return Real("g@clk")