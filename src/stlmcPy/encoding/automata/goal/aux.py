from functools import singledispatch
from itertools import product
from typing import Dict, List

from .label import *
from ...robust.relaxing import strengthening
from ....constraints.aux.operations import inf, sup, reduce_not
from ....constraints.constraints import *


class LabelGenerator:
    def __init__(self, formula: Formula, **args):
        if "threshold" in args:
            self._threshold = float(args["threshold"])
        else:
            raise Exception("threshold should be given")

        self._formula = formula

    def expand(self, label: Label, depth: int):
        return _expand(label, depth, self._threshold)

    def init(self):
        return _init(self._formula, self._threshold)


def _expand(label: Label, depth: int, threshold: float) -> Set[Label]:
    c, n, f = label.cur, label.nxt, label.forbidden
    labels: Set[Label] = set()

    # do not expand when next is empty
    if len(n) <= 0:
        return set()

    waiting_list = [(n.copy(), empty_label())]
    loop = 0
    while len(waiting_list) > 0:
        p_c, p_l = waiting_list.pop()
        if len(p_c) <= 0:
            labels.add(p_l)
            continue

        loop += 1
        p_f = p_c.pop()
        lbs = _label_expand(p_f, c, depth, threshold)

        update_queue = update_waiting_list(p_f, lbs, (p_c, p_l))
        update_queue = _remove_invalid_label(update_queue)
        update_queue = _remove_unreachable(update_queue)

        waiting_list.extend(update_queue)

    # print("# iteration {}".format(loop))
    return labels


def _init(formula: Formula, threshold: float):
    s_label = Label(singleton(), singleton(formula), singleton(), singleton())
    return _expand(s_label, 1, threshold)


@singledispatch
def _label_expand(formula: Formula, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    raise Exception("cannot find a matching rule ({})".format(formula))


@_label_expand.register(Proposition)
def _(formula: Proposition, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    return {Label(singleton(), singleton(), singleton(), singleton())}


@_label_expand.register(GloballyFormula)
def _(formula: GloballyFormula, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    if is_untimed(formula.local_time):
        lb1 = Label(singleton(formula.child), singleton(formula), singleton(), singleton())
        lb2 = Label(singleton(formula.child, TimeLast()), singleton(), singleton(), singleton())
        return {lb1, lb2}
    else:
        if formula not in ctx:
            f, start, interval = formula.child, symbolic_interval(depth), formula.local_time

            f1, f2 = GloballyUp(start, interval, f), GloballyUpIntersect(interval, f)
            f3, f4 = GloballyUpDown(start, start, interval, f), GloballyUpIntersectDown(start, interval, f)
            t_pre = TimePre(start, interval)
            t_in = TimeIntersect(start, interval)

            lb1 = Label(singleton(f1, t_pre), singleton(), singleton(), singleton())
            lb2 = Label(singleton(f2, t_in), singleton(), singleton(), singleton())
            lb3 = Label(singleton(f3, t_pre), singleton(), singleton(), singleton())
            lb4 = Label(singleton(f4, t_in), singleton(), singleton(), singleton())
            return {lb1, lb2, lb3, lb4}
        else:
            return {empty_label()}


@_label_expand.register(GloballyUp)
def _(formula: GloballyUp, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    f, base, n_interval, interval = formula.child, formula.i, symbolic_interval(depth + 1), formula.interval
    pre = TimePre(base, interval)
    its = TimeIntersect(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUp(base, interval, f)
    f2 = GloballyUpIntersect(interval, f)
    f3 = GloballyUpDown(base, n_interval, interval, f)
    f4 = GloballyUpIntersectDown(n_interval, interval, f)
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(), singleton(f1, pre), singleton(), singleton(nxt))
    label2 = Label(singleton(), singleton(f2, its), singleton(), singleton(nxt))
    label3 = Label(singleton(), singleton(f3, pre), singleton(), singleton(nxt))
    label4 = Label(singleton(), singleton(f4, its), singleton(), singleton(nxt))
    return {label1, label2, label3, label4}


@_label_expand.register(GloballyUpDown)
def _(formula: GloballyUpDown, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    f = formula.child
    base, end, cur, interval = formula.i, formula.k, symbolic_interval(depth), formula.interval

    pre = TimePre(base, interval)
    tls = TimeLast()
    its = TimeIntersect(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUpIntersectDown(end, interval, f)
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(), singleton(f1, its), singleton(nxt), singleton())
    label2 = Label(singleton(), singleton(formula, pre), singleton(nxt), singleton())
    label3 = Label(singleton(tls), singleton(), singleton(), singleton())

    return {label1, label2, label3}


@_label_expand.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    f, end, interval = formula.child, symbolic_interval(depth), formula.interval

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUpIntersectDown(end, interval, f)
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(), singleton(f1), singleton(), singleton(nxt))
    label2 = Label(singleton(f), singleton(formula), singleton(), singleton(nxt))

    return {label1, label2}


@_label_expand.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    f, end, current, interval = formula.child, formula.i, symbolic_interval(depth), formula.interval

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    tps = TimePost(end, interval)
    # n_tps = TimeNotPost(end, interval)
    tls = TimeLast()
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(tps, f), singleton(), singleton(nxt), singleton())
    label2 = Label(singleton(tls, f), singleton(), singleton(nxt), singleton())
    label3 = Label(singleton(f), singleton(formula), singleton(nxt), singleton())

    return {label1, label2, label3}


@_label_expand.register(FinallyFormula)
def _(formula: FinallyFormula, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    if is_untimed(formula.local_time):
        label1 = Label(singleton(formula.child), singleton(), singleton(), singleton())
        label2 = Label(singleton(), singleton(formula), singleton(), singleton())
        return {label1, label2}
    else:
        if formula not in ctx:
            cur, interval, f = symbolic_interval(depth), formula.local_time, formula.child

            t_pre = TimePreFinally(cur, interval)
            t_in = TimeIntersectFinally(cur, interval)
            f1, f2 = FinallyUp(cur, interval, f), FinallyUpIntersect(interval, f)
            f3, f4 = FinallyUpDown(cur, cur, interval, f), FinallyUpIntersectDown(cur, interval, f)

            label1 = Label(singleton(f1, t_pre), singleton(), singleton(), singleton())
            label2 = Label(singleton(f2, f, t_in), singleton(), singleton(), singleton())
            label3 = Label(singleton(f3, t_pre), singleton(), singleton(), singleton())
            label4 = Label(singleton(f4, f, t_in), singleton(), singleton(), singleton())

            return {label1, label2, label3, label4}
        else:
            return {empty_label()}


@_label_expand.register(FinallyUp)
def _(formula: FinallyUp, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    f, base, nxt_interval, interval = formula.child, formula.i, symbolic_interval(depth + 1), formula.interval
    t_pre = TimePreFinally(base, interval)
    t_in = TimeIntersectFinally(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1, f2 = FinallyUp(base, interval, f), FinallyUpIntersect(interval, f)
    f3, f4 = FinallyUpDown(base, nxt_interval, interval, f), FinallyUpIntersectDown(nxt_interval, interval, f)
    nxt = FinallyFormula(interval, g, f)

    label1 = Label(singleton(), singleton(f1, t_pre), singleton(), singleton(nxt))
    label2 = Label(singleton(), singleton(t_in, f, f2), singleton(), singleton(nxt))
    label3 = Label(singleton(), singleton(f3, t_pre), singleton(), singleton(nxt))
    label4 = Label(singleton(), singleton(f4, f, t_in), singleton(), singleton(nxt))

    return {label1, label2, label3, label4}


@_label_expand.register(FinallyUpDown)
def _(formula: FinallyUpDown, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    f, base, end, interval = formula.child, formula.i, formula.k, formula.interval
    t_pre = TimePreFinally(base, interval)
    t_in = TimeIntersectFinally(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    nxt = FinallyFormula(interval, g, f)

    f1 = FinallyUpIntersectDown(end, interval, f)
    label1 = Label(singleton(), singleton(t_pre, formula), singleton(nxt), singleton())
    label2 = Label(singleton(), singleton(f, t_in, f1), singleton(nxt), singleton())

    return {label1, label2}


@_label_expand.register(FinallyUpIntersect)
def _(formula: FinallyUpIntersect, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    cur, f, interval = symbolic_interval(depth), formula.child, formula.interval
    nxt_interval = symbolic_interval(depth + 1)
    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    nxt = FinallyFormula(interval, g, f)

    n_interval = Interval(True, sup(cur - interval), Real("tau_max"), False)
    f1 = FinallyUp(n_interval, interval, f)
    f2 = FinallyUpIntersectDown(nxt_interval, interval, f)

    label1 = Label(singleton(), singleton(f, formula), singleton(), singleton(nxt))
    label2 = Label(singleton(), singleton(f1, _nnf(f, threshold)), singleton(), singleton(nxt))
    label3 = Label(singleton(), singleton(f2, f), singleton(), singleton(nxt))

    return {label1, label2, label3}


@_label_expand.register(FinallyUpIntersectDown)
def _(formula: FinallyUpIntersectDown, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    end, f, interval = formula.i, formula.child, formula.interval
    cur = symbolic_interval(depth)
    lst = TimePostFinally(end, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    nxt = FinallyFormula(interval, g, f)
    n_interval = Interval(True, sup(cur - interval), Real("tau_max"), False)

    f1 = FinallyUpDown(n_interval, end, interval, f)

    label1 = Label(singleton(lst), singleton(), singleton(nxt), singleton())
    label2 = Label(singleton(), singleton(formula, f), singleton(nxt), singleton())
    label3 = Label(singleton(), singleton(f1, _nnf(f, threshold)), singleton(nxt), singleton())

    return {label1, label2, label3}


@_label_expand.register(UntilFormula)
def _(formula: UntilFormula, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    lf, rf, interval = formula.left, formula.right, formula.local_time
    assert is_untimed(interval)

    lb1 = Label(singleton(lf), singleton(formula), singleton(), singleton())
    lb2 = Label(singleton(lf, rf), singleton(), singleton(), singleton())
    return {lb1, lb2}


@_label_expand.register(ReleaseFormula)
def _(formula: ReleaseFormula, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    lf, rf, interval = formula.left, formula.right, formula.local_time
    assert is_untimed(interval)

    lb1 = Label(singleton(lf), singleton(), singleton(), singleton())
    lb2 = Label(singleton(rf, TimeLast()), singleton(), singleton(), singleton())
    lb3 = Label(singleton(rf), singleton(formula), singleton(), singleton())
    return {lb1, lb2, lb3}


@_label_expand.register(And)
def _(formula: And, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    assert len(formula.children) == 2
    lf, rf = formula.children[0], formula.children[1]
    return {Label(singleton(lf, rf), singleton(), singleton(), singleton())}


@_label_expand.register(Or)
def _(formula: Or, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
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


def _apply_forbidden(waiting_queue: List[Tuple[Set[Formula], Label]],
                     forbidden: Set[Formula]) -> List[Tuple[Set[Formula], Label]]:
    n_queue = list()
    for p_c, p_l in waiting_queue:
        if not p_l.cur.intersection(forbidden):
            n_queue.append((p_c, p_l))
    return n_queue


def _remove_invalid_label(waiting_queue: List[Tuple[Set[Formula], Label]]) -> List[Tuple[Set[Formula], Label]]:
    n_queue = list()
    for p_c, p_l in waiting_queue:
        f, a = p_l.forbidden, p_l.assertion
        if not p_l.nxt.intersection(f) and a.issubset(p_l.nxt):
            n_queue.append((p_c, p_l))
    return n_queue


def _remove_unreachable(waiting_queue: List[Tuple[Set[Formula], Label]]) -> List[Tuple[Set[Formula], Label]]:
    n_queue = list()
    for p_c, p_l in waiting_queue:
        c, n = p_l.cur, p_l.nxt
        c = set(filter(lambda x: isinstance(x, TimeLast), c))
        # time last cannot have next states
        if len(c) > 0 and len(n) > 0:
            continue

        n_queue.append((p_c, p_l))
    return n_queue


def update_labels(formula: Formula, labels: Set[Label], label: Label) -> List[Tuple[Set[Formula], Label]]:
    return [(lb.cur, Label(label.cur.union({formula}), label.nxt.union(lb.nxt),
                           label.forbidden.union(lb.forbidden),
                           label.assertion.union(lb.assertion))) for lb in labels]


def empty_label() -> Label:
    return Label(singleton(), singleton(), singleton(), singleton())


def singleton(*formulas) -> Set[Formula]:
    return set(formulas)


def intersection(interval1: Interval, interval2: Interval):
    return inf(interval1) <= sup(interval2), inf(interval2) <= sup(interval1)


def symbolic_interval(num: int):
    # [tau_{num - 1}, tau_{num})
    l_n, r_n = num - 1, num
    lv = Real("tau_{}".format(l_n))
    rv = Real("tau_{}".format(r_n))
    return Interval(True, lv, rv, True)


def canonicalize(*label):
    labels: Set[Label] = set(label)
    subsume: Dict[Label, Set[Label]] = dict()
    pre_status: Dict[Label, Set[Label]] = dict()
    while True:
        _calc_label_subsume(labels, subsume)

        cur_status = subsume
        if cur_status == pre_status:
            break

        pre_status = subsume.copy()

    # ignore self
    for label in subsume:
        subsume[label].discard(label)

    removed = set()
    for label in labels:
        assert label in subsume
        if len(subsume[label]) > 0:
            removed.add(label)

    return labels.difference(removed)


def _calc_label_subsume(labels: Set[Label], subsume: Dict[Label, Set[Label]]):
    def _add_to_dict(_k: Label, *_vs):
        if _k not in subsume:
            subsume[_k] = {_v for _v in _vs}
        else:
            for _v in _vs:
                subsume[_k].add(_v)

    for label in labels:
        waiting = labels.copy()
        while len(waiting) > 0:
            n = waiting.pop()
            if _label_subsume(n, label):
                _add_to_dict(label, n)
                if n in subsume:
                    _add_to_dict(label, *subsume[n])
                    waiting.difference_update(subsume[n])


def _label_subsume(label1: Label, label2: Label) -> bool:
    c1 = label1.cur.issubset(label2.cur)
    c2 = label1.nxt.issubset(label2.nxt)
    c3 = label1.forbidden.issubset(label2.forbidden)
    return c1 and c2 and c3


def tau_max():
    return Real("tau_max")


def translate(label: Label, depth: int) -> Tuple[Set[Formula], Set[Formula]]:
    non_intermediate, intermediate = split_label(label)
    f_s = set()
    for lb_f in non_intermediate:
        try:
            f_s.add(translate_formula(lb_f, depth))
        except Exception:
            raise Exception("fail to translate a label ({})".format(label))
    return f_s, intermediate


def translate_formula(formula: Formula, depth: int) -> Formula:
    if isinstance(formula, TimeProposition):
        return _time_translate(formula, depth)
    elif isinstance(formula, Proposition):
        return formula
    else:
        raise Exception("fail to translate a formula ({})".format(formula))


@singledispatch
def _time_translate(formula: TimeProposition, depth: int) -> Formula:
    raise Exception("cannot translate {} to a time formula".format(formula))


@_time_translate.register(TimeLast)
def _(formula: TimeLast, depth: int) -> Formula:
    cur = symbolic_interval(depth)
    return sup(cur) >= tau_max()


@_time_translate.register(TimeIntersect)
def _(formula: TimeIntersect, depth: int) -> Formula:
    cur = symbolic_interval(depth)
    return And([inf(cur) <= inf(formula.i) + inf(formula.interval),
                inf(formula.i) + inf(formula.interval) <= sup(cur)])


@_time_translate.register(TimePre)
def _(formula: TimePre, depth: int) -> Formula:
    cur = symbolic_interval(depth)
    return sup(cur) <= inf(formula.i) + inf(formula.interval)


@_time_translate.register(TimePost)
def _(formula: TimePost, depth: int) -> Formula:
    cur = symbolic_interval(depth)
    return And([inf(cur) <= sup(formula.i) + sup(formula.interval),
                sup(formula.i) + sup(formula.interval) <= sup(cur)])


@_time_translate.register(TimeNotPost)
def _(formula: TimeNotPost, depth: int) -> Formula:
    cur = symbolic_interval(depth)
    return sup(cur) <= sup(formula.i) + sup(formula.interval)


@_time_translate.register(TimePreFinally)
def _(formula: TimePreFinally, depth: int) -> Formula:
    base, cur, interval = formula.i, symbolic_interval(depth), formula.interval
    return inf(cur - interval) <= inf(base)


@_time_translate.register(TimeIntersectFinally)
def _(formula: TimeIntersectFinally, depth: int) -> Formula:
    base, cur, interval = formula.i, symbolic_interval(depth), formula.interval
    target = cur - interval
    return And([inf(target) <= inf(base), inf(base) <= sup(target)])


@_time_translate.register(TimePostFinally)
def _(formula: TimePostFinally, depth: int) -> Formula:
    base, cur, interval = formula.i, symbolic_interval(depth), formula.interval
    target = cur - interval
    return And([inf(target) <= sup(base), sup(base) <= sup(target)])


def split_label(label: Label) -> Tuple[Set[Formula], Set[Formula]]:
    non_intermediate, intermediate = set(), set()
    for lb in label.cur:
        if isinstance(lb, Proposition):
            non_intermediate.add(lb)
        else:
            intermediate.add(lb)
    return non_intermediate, intermediate


def stuttering(label: Label, labels: Set[Label], depth: int) -> Set[Label]:
    removed = set()
    for lb in labels:
        if _stuttering_equivalent(label, lb):
            removed.add(lb)
    return labels.difference(removed)


def _stuttering_equivalent(label1: Label, label2: Label):
    filters = {
        # general
        "non-time": lambda x: not isinstance(x, TimeProposition),

        # trigger filter
        "up[]": lambda x: isinstance(x, GloballyUp),
        "up[*]": lambda x: isinstance(x, GloballyUpIntersect),
        "up<>": lambda x: isinstance(x, FinallyUp),
        "up<*>": lambda x: isinstance(x, FinallyUpIntersect),

        "up&down[]": lambda x: isinstance(x, GloballyUpDown),
        "up[*]down[]": lambda x: isinstance(x, GloballyUpIntersectDown),
        "up&down<>": lambda x: isinstance(x, FinallyUpDown),
        "up<*>down<>": lambda x: isinstance(x, FinallyUpIntersectDown)
    }

    c1, c2 = set(filter(filters["non-time"], label1.cur)), set(filter(filters["non-time"], label2.cur))

    c1_cg = [set(filter(filters["up[]"], c1)), set(filter(filters["up[*]"], c1)),
             set(filter(filters["up<>"], c1)), set(filter(filters["up<*>"], c1))]

    c2_cg = [set(filter(filters["up&down[]"], c2)), set(filter(filters["up[*]down[]"], c2)),
             set(filter(filters["up&down<>"], c2)), set(filter(filters["up<*>down<>"], c2))]

    pair = set()
    for idx, c1_fs in enumerate(c1_cg):
        c2_fs = c2_cg[idx]
        for f1, f2 in product(c1_fs, c2_fs):
            if _stuttering_pair(f1, f2):
                pair.add((f1, f2))

    c1_cpy, c2_cpy = c1.copy(), c2.copy()
    for f1, f2 in pair:
        c1_cpy.remove(f1)
        c2_cpy.remove(f2)

    return c1_cpy == c2_cpy


def _stuttering_pair(cur: Formula, nxt: Formula) -> bool:
    types = [
        isinstance(cur, GloballyUp) and isinstance(nxt, GloballyUpDown),
        isinstance(cur, GloballyUpIntersect) and isinstance(nxt, GloballyUpIntersectDown),
        isinstance(cur, FinallyUp) and isinstance(nxt, FinallyUpDown),
        isinstance(cur, FinallyUpIntersect) and isinstance(nxt, FinallyUpIntersectDown)
    ]
    if any(types):
        assert isinstance(cur, Up) or isinstance(cur, UpIntersect)
        assert isinstance(nxt, UpDown) or isinstance(nxt, UpIntersectionDown)
        return cur.interval == nxt.interval and hash(cur.child) == hash(nxt.child)
    else:
        return False


def is_untimed(interval: Interval):
    untimed = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    return interval == untimed


def _nnf(formula: Formula, threshold: float):
    f = strengthening(formula, threshold)
    return reduce_not(Not(f))
