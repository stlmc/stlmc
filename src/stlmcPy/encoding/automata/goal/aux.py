from typing import Tuple

from .clock import *
from .label import *
from ...robust.relaxing import strengthening
from ....constraints.aux.operations import inf, reduce_not
from ....constraints.constraints import *

clk_gen = ClockGenerator()


def expand(*labels) -> Set[Label]:
    lb_s: Set[Label] = set()
    for label in labels:
        lb_s.update(_expand(label))
    return lb_s


def _expand(label: Label) -> Set[Label]:
    labels: Set[Label] = set()

    # do not expand when next is empty
    if len(label.nxt) <= 0:
        return set()

    empty_label = Label(singleton(), label.transition_nxt, singleton(), singleton())
    waiting_list = [(label.state_nxt.copy(), empty_label)]

    while len(waiting_list) > 0:
        p_c, p_l = waiting_list.pop()
        if len(p_c) <= 0:
            labels.add(p_l)
            continue

        p_f = p_c.pop()
        lbs = _label_expand(p_f)

        # check if refinement is needed
        lbs = _refine_globally_labels(label, lbs)
        lbs = _refine_finally_labels(label, lbs)

        update_queue = update_waiting_list(p_f, lbs, (p_c, p_l))
        waiting_list.extend(update_queue)

    labels = _remove_invalid_globally_label(label, labels)
    labels = _remove_invalid_finally_label(label, labels)
    labels = _remove_unreachable(labels)
    labels = _remove_clock_violation(labels)

    return labels


@singledispatch
def _label_expand(formula: Formula) -> Set[Label]:
    raise Exception("cannot find a matching rule ({})".format(formula))


@_label_expand.register(Proposition)
def _(formula: Proposition) -> Set[Label]:
    return {Label(singleton(), singleton(), singleton(), singleton())}


@_label_expand.register(GloballyFormula)
def _(formula: GloballyFormula) -> Set[Label]:
    if is_untimed(formula.local_time):
        lb1 = Label(singleton(formula.child), singleton(), singleton(formula), singleton())
        lb2 = Label(singleton(formula.child), singleton(), singleton(), singleton(TimeBound()))
        return {lb1, lb2}
    else:
        f, interval = formula.child, formula.local_time

        clk = clk_gen.up_clock(formula)
        r_clk = ClkReset(clk)

        ty = TypeVariable(clk.id)
        oc = OpenClose(ty)
        f1, f2 = GloballyUp(clk, ty, interval, f), GloballyUpIntersect(clk, ty, interval, f)

        lb1 = Label(singleton(f1), singleton(oc, r_clk), singleton(), singleton())
        lb2 = Label(singleton(f2), singleton(oc, r_clk), singleton(), singleton())

        return {lb1, lb2}


@_label_expand.register(GloballyUp)
def _(formula: GloballyUp) -> Set[Label]:
    t_pre = TimeGloballyPre(formula.clock, formula.type, formula.interval)
    new_f = GloballyUpIntersect(formula.clock, formula.type, formula.interval, formula.formula)

    lb1 = Label(singleton(), singleton(), singleton(formula), singleton(t_pre))
    lb2 = Label(singleton(), singleton(), singleton(new_f), singleton(t_pre))
    lb3 = Label(singleton(), singleton(), singleton(), singleton(t_pre, TimeBound()))

    f, interval = formula.formula, formula.interval
    clk1, ty1 = formula.clock, formula.type
    clk2 = clk_gen.down_clock(_infer_temporal_formula(formula), clk1)
    ty2 = TypeVariable(clk2.id)
    r_clk = ClkReset(clk2)

    f1 = GloballyUpDown(clk1, clk2, ty1, ty2, interval, f)
    f2 = GloballyUpIntersectDown(clk1, clk2, ty1, ty2, interval, f)
    oc = OpenClose(ty2)

    lb4 = Label(singleton(), singleton(), singleton(f1), singleton(t_pre, oc, r_clk))
    lb5 = Label(singleton(), singleton(), singleton(f2), singleton(t_pre, oc, r_clk))
    return {lb1, lb2, lb3, lb4, lb5}


@_label_expand.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect) -> Set[Label]:
    f, interval = formula.formula, formula.interval
    lb1 = Label(singleton(f), singleton(), singleton(formula), singleton())
    lb2 = Label(singleton(f), singleton(), singleton(), singleton(TimeBound()))

    clk1, ty1 = formula.clock, formula.type
    clk2 = clk_gen.down_clock(_infer_temporal_formula(formula), clk1)
    ty2 = TypeVariable(clk2.id)
    r_clk = ClkReset(clk2)

    f1 = GloballyUpIntersectDown(clk1, clk2, ty1, ty2, interval, f)
    oc = OpenClose(ty2)

    lb3 = Label(singleton(f), singleton(), singleton(f1), singleton(oc, r_clk))
    return {lb1, lb2, lb3}


@_label_expand.register(GloballyUpDown)
def _(formula: GloballyUpDown) -> Set[Label]:
    t_pre = TimeGloballyPre(formula.clock[0], formula.type[0], formula.interval)
    f = GloballyUpIntersectDown(formula.clock[0], formula.clock[1], formula.type[0], formula.type[1],
                                formula.interval, formula.formula)

    lb1 = Label(singleton(), singleton(), singleton(formula), singleton(t_pre))
    lb2 = Label(singleton(), singleton(), singleton(f), singleton(t_pre))
    lb3 = Label(singleton(), singleton(), singleton(), singleton(t_pre, TimeBound()))

    return {lb1, lb2, lb3}


@_label_expand.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown) -> Set[Label]:
    t_final = TimeGloballyFinal(formula.clock[1], formula.type[1], formula.interval)

    lb1 = Label(singleton(formula.formula), singleton(), singleton(formula), singleton())
    lb2 = Label(singleton(formula.formula), singleton(), singleton(), singleton(t_final))
    lb3 = Label(singleton(formula.formula), singleton(), singleton(), singleton(TimeBound()))

    return {lb1, lb2, lb3}


@_label_expand.register(FinallyFormula)
def _(formula: FinallyFormula) -> Set[Label]:
    f, interval = formula.child, formula.local_time

    clk = clk_gen.up_clock(formula)
    ty = TypeVariable(clk.id)
    oc = OpenClose(ty)
    r_clk = ClkReset(clk)

    f1, f2 = FinallyUp(clk, ty, interval, f), FinallyUpIntersect(clk, ty, interval, f)

    lb1 = Label(singleton(f1), singleton(oc, r_clk), singleton(), singleton())
    lb2 = Label(singleton(f2), singleton(oc, r_clk), singleton(), singleton())

    return {lb1, lb2}


@_label_expand.register(FinallyUp)
def _(formula: FinallyUp) -> Set[Label]:
    t_pre = TimeFinallyPre(formula.clock, formula.type, formula.interval)
    new_f = FinallyUpIntersect(formula.clock, formula.type, formula.interval, formula.formula)

    lb1 = Label(singleton(), singleton(), singleton(formula), singleton(t_pre))
    lb2 = Label(singleton(), singleton(), singleton(new_f), singleton(t_pre))

    f, interval = formula.formula, formula.interval
    clk1, ty1 = formula.clock, formula.type
    clk2 = clk_gen.down_clock(_infer_temporal_formula(formula), clk1)
    ty2 = TypeVariable(clk2.id)
    r_clk = ClkReset(clk2)
    oc = OpenClose(ty2)

    f1 = FinallyUpDown(clk1, clk2, ty1, ty2, interval, f)
    f2 = FinallyUpIntersectDown(clk1, clk2, ty1, ty2, interval, f)

    lb3 = Label(singleton(), singleton(), singleton(f1), singleton(t_pre, oc, r_clk))
    lb4 = Label(singleton(), singleton(), singleton(f2), singleton(t_pre, oc, r_clk))
    return {lb1, lb2, lb3, lb4}


@_label_expand.register(FinallyUpIntersect)
def _(formula: FinallyUpIntersect) -> Set[Label]:
    f, interval = formula.formula, formula.interval
    clk, ty = formula.clock, formula.type

    lb1 = Label(singleton(f), singleton(), singleton(formula), singleton())
    lb2 = Label(singleton(f), singleton(), singleton(), singleton(TimeBound()))

    r_clk = ClkAssn(clk, inf(interval))

    nf = FinallyUp(clk, ty, interval, f)
    rst = TimeFinallyRestart(clk, ty, interval)

    if interval.left_end:
        oc1 = Close(ty)
    else:
        oc1 = Open(ty)

    lb3 = Label(singleton(f), singleton(), singleton(nf), singleton(r_clk, rst, oc1))

    # introduce a new clock
    clk2 = clk_gen.down_clock(_infer_temporal_formula(formula), clk)
    ty2 = TypeVariable(clk2.id)
    oc2 = OpenClose(ty2)
    r_clk2 = ClkReset(clk2)

    f1 = FinallyUpDown(clk, clk2, ty, ty2, interval, f)
    f2 = FinallyUpIntersectDown(clk, clk2, ty, ty2, interval, f)

    lb4 = Label(singleton(f), singleton(), singleton(f1), singleton(r_clk, r_clk2, rst, oc2))
    lb5 = Label(singleton(f), singleton(), singleton(f2), singleton(r_clk2, oc2))

    return {lb1, lb2, lb3, lb4, lb5}


@_label_expand.register(FinallyUpDown)
def _(formula: FinallyUpDown) -> Set[Label]:
    t_pre = TimeFinallyPre(formula.clock[0], formula.type[0], formula.interval)
    nf = FinallyUpIntersectDown(formula.clock[0], formula.clock[1],
                                formula.type[0], formula.type[1],
                                formula.interval, formula.formula)

    lb1 = Label(singleton(), singleton(), singleton(formula), singleton(t_pre))
    lb2 = Label(singleton(), singleton(), singleton(nf), singleton(t_pre))

    return {lb1, lb2}


@_label_expand.register(FinallyUpIntersectDown)
def _(formula: FinallyUpIntersectDown) -> Set[Label]:
    f, clk1, clk2 = formula.formula, formula.clock[0], formula.clock[1]
    ty1, ty2, interval = formula.type[0], formula.type[1], formula.interval
    nf = FinallyUpDown(clk1, clk2, ty1, ty2, interval, f)

    r_clk1 = ClkAssn(clk1, inf(interval))
    r_clk2 = ClkReset(clk2)

    rst = TimeFinallyRestart(clk1, ty1, interval)

    if interval.left_end:
        oc = Close(ty1)
    else:
        oc = Open(ty1)

    final = TimeFinallyFinal(clk2, ty2, interval)

    lb1 = Label(singleton(f), singleton(), singleton(formula), singleton())
    lb2 = Label(singleton(f), singleton(), singleton(nf), singleton(r_clk1, r_clk2, oc, rst))
    lb3 = Label(singleton(f), singleton(), singleton(), singleton(TimeBound()))
    lb4 = Label(singleton(f), singleton(), singleton(), singleton(final))

    return {lb1, lb2, lb3, lb4}


@_label_expand.register(UntilFormula)
def _(formula: UntilFormula) -> Set[Label]:
    lf, rf, interval = formula.left, formula.right, formula.local_time
    assert is_untimed(interval)

    lb1 = Label(singleton(lf), singleton(), singleton(formula), singleton())
    lb2 = Label(singleton(lf, rf), singleton(), singleton(), singleton())
    return {lb1, lb2}


@_label_expand.register(ReleaseFormula)
def _(formula: ReleaseFormula) -> Set[Label]:
    lf, rf, interval = formula.left, formula.right, formula.local_time
    assert is_untimed(interval)

    lb1 = Label(singleton(lf), singleton(), singleton(), singleton())
    lb2 = Label(singleton(rf), singleton(), singleton(), singleton(TimeBound()))
    lb3 = Label(singleton(rf), singleton(), singleton(formula), singleton())
    return {lb1, lb2, lb3}


@_label_expand.register(And)
def _(formula: And) -> Set[Label]:
    assert len(formula.children) == 2
    lf, rf = formula.children[0], formula.children[1]
    return {Label(singleton(lf, rf), singleton(), singleton(), singleton())}


@_label_expand.register(Or)
def _(formula: Or) -> Set[Label]:
    assert len(formula.children) == 2
    lf, rf = formula.children[0], formula.children[1]
    return {Label(singleton(lf), singleton(), singleton(), singleton()),
            Label(singleton(rf), singleton(), singleton(), singleton())}


def update_waiting_list(formula: Formula, labels: Set[Label],
                        elem: Tuple[Set[Formula], Label]) -> List[Tuple[Set[Formula], Label]]:
    w_f, lb = elem

    # update label
    lbs = update_labels(formula, labels, lb)
    return [(w_f.union(nc), u_lb) for nc, u_lb in lbs]


def _remove_invalid_globally_label(label: Label, labels: Set[Label]) -> Set[Label]:
    return set(filter(lambda x: not _invalid_globally_label(label, x), labels))


def _remove_invalid_finally_label(label: Label, labels: Set[Label]) -> Set[Label]:
    return set(filter(lambda x: not _invalid_finally_label(label, x), labels))


def _refine_globally_labels(label: Label, labels: Set[Label]) -> Set[Label]:
    lb_s = set()
    for lb in labels:
        if not _refine_globally_label(label, lb):
            lb_s.add(lb)
        else:
            lb_s.add(Label(singleton(), singleton(), singleton(), singleton()))
    return lb_s


def _refine_finally_labels(label: Label, labels: Set[Label]) -> Set[Label]:
    lb_s = set()
    for lb in labels:
        if not _refine_finally_label(label, lb):
            lb_s.add(lb)
        else:
            lb_s.add(Label(singleton(), singleton(), singleton(), singleton()))
    return lb_s


def _invalid_globally_label(cur_label: Label, nxt_label: Label) -> bool:
    # find globally temporal formulas in the current goals
    g_cur = set(filter(lambda x: isinstance(x, GloballyFormula), cur_label.cur))
    g_nxt = set(filter(lambda x: isinstance(x, GloballyFormula), nxt_label.cur))

    # case 1) if a new goal has up and up intersect goals with a new clock
    nxt_clk_g = set(filter(lambda x: isinstance(x, ClkReset), nxt_label.cur))
    nxt_clk_s = set(map(lambda x: x.clock, nxt_clk_g))

    for g_f in g_cur:
        assert isinstance(g_f, GloballyFormula)
        if g_f not in g_nxt:
            # there should be i) updowns or ii) time bound in the next goals
            valid = _get_globally_up_downs(g_f, nxt_clk_s, *nxt_label.cur)
            is_tb = TimeBound() in nxt_label.cur

            if len(valid) <= 0 and not is_tb:
                return True
        else:
            # because next goal contains global operator g_f,
            # there should be no updown
            invalid = _get_globally_up_downs(g_f, nxt_clk_s, *nxt_label.cur)

            if len(invalid) > 0:
                return True

    # valid case
    return False


def _refine_globally_label(cur_label: Label, nxt_label: Label) -> bool:
    # find globally temporal formulas in the current goals
    g_cur = set(filter(lambda x: isinstance(x, GloballyFormula), cur_label.cur))

    # find clock resets
    nxt_clk_g = set(filter(lambda x: isinstance(x, ClkReset), nxt_label.cur))
    nxt_clk_s = set(map(lambda x: x.clock, nxt_clk_g))

    for g_f in g_cur:
        assert isinstance(g_f, GloballyFormula)
        # if a new goal has up and up intersect goals with a new clock
        potential = _get_globally_ups(g_f, nxt_clk_s, *nxt_label.cur)

        if len(potential) > 0:
            return True

    return False


def _invalid_finally_label(cur_label: Label, nxt_label: Label) -> bool:
    # find globally temporal formulas in the current goals
    f_cur = set(filter(lambda x: isinstance(x, FinallyFormula), cur_label.cur))
    f_nxt = set(filter(lambda x: isinstance(x, FinallyFormula), nxt_label.cur))

    # case 1) if a new goal has up and up intersect goals with a new clock
    nxt_clk_g = set(filter(lambda x: isinstance(x, ClkReset), nxt_label.cur))
    nxt_clk_s = set(map(lambda x: x.clock, nxt_clk_g))

    for f_f in f_cur:
        assert isinstance(f_f, FinallyFormula)
        if f_f not in f_nxt:
            # there should be i) updowns or ii) time bound in the next goals
            valid = _get_finally_up_downs(f_f, nxt_clk_s, *nxt_label.cur)
            is_tb = TimeBound() in nxt_label.cur

            if len(valid) <= 0 and not is_tb:
                return True
        else:
            # because next goal contains final operator f_f,
            # there should be no updown
            invalid = _get_finally_up_downs(f_f, nxt_clk_s, *nxt_label.cur)

            if len(invalid) > 0:
                return True

    # valid case
    return False


def _refine_finally_label(cur_label: Label, nxt_label: Label) -> bool:
    # find finally temporal formulas in the current goals
    g_cur = set(filter(lambda x: isinstance(x, FinallyFormula), cur_label.cur))

    # find clock resets
    nxt_clk_g = set(filter(lambda x: isinstance(x, ClkReset), nxt_label.cur))
    nxt_clk_s = set(map(lambda x: x.clock, nxt_clk_g))

    for g_f in g_cur:
        assert isinstance(g_f, FinallyFormula)
        # if a new goal has up and up intersect goals with a new clock
        potential = _get_finally_ups(g_f, nxt_clk_s, *nxt_label.cur)

        if len(potential) > 0:
            return True

    return False


def _get_globally_ups(base: GloballyFormula, clk_s: Set[Real], *goals) -> Set[Formula]:
    s = set()
    for g in goals:
        s.update(_get_globally_up(g, base, clk_s))
    return s


@singledispatch
def _get_globally_up(formula: Formula, base: GloballyFormula,
                     clk_s: Set[Real]) -> Set[Formula]:
    return set()


@_get_globally_up.register(GloballyUp)
def _(formula: GloballyUp, base: GloballyFormula,
      clk_s: Set[Real]) -> Set[Formula]:
    f, interval = formula.formula, formula.interval
    if base.local_time == interval and base.child == f:
        if formula.clock in clk_s:
            return {formula}
    return set()


@_get_globally_up.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect, base: GloballyFormula,
      clk_s: Set[Real]) -> Set[Formula]:
    f, interval = formula.formula, formula.interval
    if base.local_time == interval and base.child == f:
        if formula.clock in clk_s:
            return {formula}
    return set()


def _get_finally_ups(base: FinallyFormula, clk_s: Set[Real], *goals) -> Set[Formula]:
    s = set()
    for g in goals:
        s.update(_get_finally_up(g, base, clk_s))
    return s


@singledispatch
def _get_finally_up(formula: Formula, base: FinallyFormula,
                    clk_s: Set[Real]) -> Set[Formula]:
    return set()


@_get_finally_up.register(FinallyUp)
def _(formula: FinallyUp, base: FinallyFormula,
      clk_s: Set[Real]) -> Set[Formula]:
    f, interval = formula.formula, formula.interval
    if base.local_time == interval and base.child == f:
        if formula.clock in clk_s:
            return {formula}
    return set()


@_get_finally_up.register(FinallyUpIntersect)
def _(formula: FinallyUpIntersect, base: FinallyFormula,
      clk_s: Set[Real]) -> Set[Formula]:
    f, interval = formula.formula, formula.interval
    if base.local_time == interval and base.child == f:
        if formula.clock in clk_s:
            return {formula}
    return set()


def _get_globally_up_downs(base: GloballyFormula, clk_s: Set[Real], *goals) -> Set[Formula]:
    s = set()
    for g in goals:
        s.update(_get_globally_updown(g, base, clk_s))
    return s


@singledispatch
def _get_globally_updown(formula: Formula, base: GloballyFormula,
                         clk_s: Set[Real]) -> Set[Formula]:
    return set()


@_get_globally_updown.register(GloballyUpDown)
def _(formula: GloballyUpDown, base: GloballyFormula,
      clk_s: Set[Real]) -> Set[Formula]:
    f, interval = formula.formula, formula.interval
    if base.local_time == interval and base.child == f:
        if formula.clock[1] in clk_s:
            return {formula}
    return set()


@_get_globally_updown.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown, base: GloballyFormula,
      clk_s: Set[Real]) -> Set[Formula]:
    f, interval = formula.formula, formula.interval
    if base.local_time == interval and base.child == f:
        if formula.clock[1] in clk_s:
            return {formula}
    return set()


def _get_finally_up_downs(base: FinallyFormula, clk_s: Set[Real], *goals) -> Set[Formula]:
    s = set()
    for g in goals:
        s.update(_get_finally_updown(g, base, clk_s))
    return s


@singledispatch
def _get_finally_updown(formula: Formula, base: FinallyFormula,
                        clk_s: Set[Real]) -> Set[Formula]:
    return set()


@_get_finally_updown.register(FinallyUpDown)
def _(formula: FinallyUpDown, base: FinallyFormula,
      clk_s: Set[Real]) -> Set[Formula]:
    f, interval = formula.formula, formula.interval
    if base.local_time == interval and base.child == f:
        if formula.clock[1] in clk_s:
            return {formula}
    return set()


@_get_finally_updown.register(FinallyUpIntersectDown)
def _(formula: FinallyUpIntersectDown, base: FinallyFormula,
      clk_s: Set[Real]) -> Set[Formula]:
    f, interval = formula.formula, formula.interval
    if base.local_time == interval and base.child == f:
        if formula.clock[1] in clk_s:
            return {formula}
    return set()


def _remove_unreachable(labels: Set[Label]) -> Set[Label]:
    n_labels = set()
    for lb in labels:
        c, n = lb.cur, lb.nxt
        c = set(filter(lambda x: isinstance(x, TimeBound), c))
        # time bound cannot have next states
        if len(c) > 0 and len(n) > 0:
            continue

        # time bound cannot have state goals
        if len(c) > 0 and len(lb.state_cur) > 0:
            continue

        n_labels.add(lb)
    return n_labels


def _remove_clock_violation(labels: Set[Label]) -> Set[Label]:
    return set(filter(lambda x: not _violate_clock_limit(x), labels))


def _violate_clock_limit(label: Label) -> bool:
    # globally and finally goal dicts
    g_dict, f_dict = dict(), dict()
    for goal in label.cur:
        r, o = _clock_related(goal)
        if r:
            is_g, i, f, clk = o
            k = (i, f)
            if is_g:
                if k in g_dict:
                    g_dict[k].add(clk)
                else:
                    g_dict[k] = {clk}
            else:
                if k in g_dict:
                    f_dict[k].add(clk)
                else:
                    f_dict[k] = {clk}

    violation = [_check_clock_violation(g_dict),
                 _check_clock_violation(f_dict)]

    # check if any of these violate clock limit
    return any(violation)


def _check_clock_violation(d: Dict[Tuple[Interval, Formula], Set[Real]]):
    for interval, f in d:
        import math
        inf_v, sup_v = float(inf(interval).value), float(sup(interval).value)
        limit = math.ceil(sup_v/(sup_v - inf_v))

        # violate upper limit
        if len(d[(interval, f)]) > limit:
            return True
    return False


@singledispatch
def _clock_related(formula: Formula) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    return False, None


@_clock_related.register(GloballyUp)
def _(formula: GloballyUp) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    # the first element of the tuple is set to true if the given formula is a globally-formula
    return True, (True, formula.interval, formula.formula, formula.clock)


@_clock_related.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    return True, (True, formula.interval, formula.formula, formula.clock)


@_clock_related.register(GloballyUpDown)
def _(formula: GloballyUpDown) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    return True, (True, formula.interval, formula.formula, formula.clock[0])


@_clock_related.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    return True, (True, formula.interval, formula.formula, formula.clock[0])


@_clock_related.register(FinallyUp)
def _(formula: FinallyUp) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    return True, (False, formula.interval, formula.formula, formula.clock)


@_clock_related.register(FinallyUpIntersect)
def _(formula: FinallyUpIntersect) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    return True, (False, formula.interval, formula.formula, formula.clock)


@_clock_related.register(FinallyUpDown)
def _(formula: FinallyUpDown) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    return True, (False, formula.interval, formula.formula, formula.clock[0])


@_clock_related.register(FinallyUpIntersectDown)
def _(formula: FinallyUpIntersectDown) -> Tuple[bool, Optional[Tuple[bool, Interval, Formula, Real]]]:
    return True, (False, formula.interval, formula.formula, formula.clock[0])


def update_labels(formula: Formula, labels: Set[Label], label: Label) -> List[Tuple[Set[Formula], Label]]:
    return [(lb.state_cur, Label(label.state_cur.union({formula}),
                                 label.transition_cur.union(lb.transition_cur),
                                 label.state_nxt.union(lb.state_nxt),
                                 label.transition_nxt.union(lb.transition_nxt))) for lb in labels]


def singleton(*formulas) -> Set[Formula]:
    return set(formulas)


def tau_max():
    return Real("tau_max")


def translate_formula(formula: Formula, depth: int) -> Formula:
    if isinstance(formula, TimeProposition):
        return _time_translate(formula, depth)
    elif isinstance(formula, Proposition):
        return formula
    else:
        raise Exception("fail to translate a formula ({})".format(formula))


def is_untimed(interval: Interval):
    untimed = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    return interval == untimed


def _nnf(formula: Formula, threshold: float):
    f = strengthening(formula, threshold)
    return reduce_not(Not(f))


@singledispatch
def _infer_temporal_formula(formula: Formula) -> Formula:
    raise Exception("cannot infer formula")


@_infer_temporal_formula.register(GloballyUp)
def _(formula: GloballyUp):
    return GloballyFormula(formula.interval, universeInterval, formula.formula)


@_infer_temporal_formula.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect):
    return GloballyFormula(formula.interval, universeInterval, formula.formula)


@_infer_temporal_formula.register(GloballyUpDown)
def _(formula: GloballyUpDown):
    return GloballyFormula(formula.interval, universeInterval, formula.formula)


@_infer_temporal_formula.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown):
    return GloballyFormula(formula.interval, universeInterval, formula.formula)


@_infer_temporal_formula.register(FinallyUp)
def _(formula: FinallyUp):
    return FinallyFormula(formula.interval, universeInterval, formula.formula)


@_infer_temporal_formula.register(FinallyUpIntersect)
def _(formula: FinallyUpIntersect):
    return FinallyFormula(formula.interval, universeInterval, formula.formula)


@_infer_temporal_formula.register(FinallyUpDown)
def _(formula: FinallyUpDown):
    return FinallyFormula(formula.interval, universeInterval, formula.formula)


@_infer_temporal_formula.register(FinallyUpIntersectDown)
def _(formula: FinallyUpIntersectDown):
    return FinallyFormula(formula.interval, universeInterval, formula.formula)
