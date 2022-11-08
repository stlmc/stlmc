from functools import singledispatch
from typing import Dict, List, Tuple

from .label import *
from ...robust.relaxing import strengthening
from ....constraints.aux.operations import inf, sup, reduce_not
from ....constraints.constraints import *


def expand(label: Label, depth: int, threshold: float) -> Set[Label]:
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
        waiting_list.extend(update_queue)

    labels = _remove_invalid_label(labels)
    labels = _remove_unreachable(labels)

    # print("# iteration {}".format(loop))
    return labels


def init(formula: Formula, threshold: float):
    s_label = Label(singleton(), singleton(formula), singleton(), singleton())
    return expand(s_label, 1, threshold)


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
            f, start, interval = formula.child, Partition(depth), formula.local_time

            f1, f2 = GloballyUp(start, interval, f), GloballyUpIntersect(start, interval, f)
            f3, f4 = GloballyUpDown(start, start, interval, f), GloballyUpIntersectDown(start, start, interval, f)
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
    f, base, n_interval, interval = formula.child, formula.i, Partition(depth + 1), formula.interval
    pre = TimePre(base, interval)
    its = TimeIntersect(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUp(base, interval, f)
    f2 = GloballyUpIntersect(base, interval, f)
    f3 = GloballyUpDown(base, n_interval, interval, f)
    f4 = GloballyUpIntersectDown(base, n_interval, interval, f)
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(), singleton(f1, pre), singleton(), singleton(nxt))
    label2 = Label(singleton(), singleton(f2, its), singleton(), singleton(nxt))
    label3 = Label(singleton(), singleton(f3, pre), singleton(), singleton(nxt))
    label4 = Label(singleton(), singleton(f4, its), singleton(), singleton(nxt))
    return {label1, label2, label3, label4}


@_label_expand.register(GloballyUpDown)
def _(formula: GloballyUpDown, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    f = formula.child
    base, end, interval = formula.i, formula.k, formula.interval

    pre = TimePre(base, interval)
    tls = TimeLast()
    its = TimeIntersect(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUpIntersectDown(base, end, interval, f)
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(), singleton(f1, its), singleton(nxt), singleton())
    label2 = Label(singleton(), singleton(formula, pre), singleton(nxt), singleton())
    label3 = Label(singleton(tls), singleton(), singleton(nxt), singleton())

    return {label1, label2, label3}


@_label_expand.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    base, f, end, interval = formula.i, formula.child, Partition(depth + 1), formula.interval

    its = TimeIntersect(base, interval)
    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUpIntersectDown(base, end, interval, f)
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(f), singleton(f1, its), singleton(), singleton(nxt))
    label2 = Label(singleton(f), singleton(formula, its), singleton(), singleton(nxt))

    return {label1, label2}


@_label_expand.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    base, f, end, interval = formula.i, formula.child, formula.k, formula.interval

    its = TimeIntersect(base, interval)
    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    tps = TimePost(end, interval)
    # n_tps = TimeNotPost(end, interval)
    tls = TimeLast()
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(tps, f), singleton(), singleton(nxt), singleton())
    label2 = Label(singleton(tls, f), singleton(), singleton(nxt), singleton())
    label3 = Label(singleton(f), singleton(formula, its), singleton(nxt), singleton())

    return {label1, label2, label3}


@_label_expand.register(FinallyFormula)
def _(formula: FinallyFormula, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    if is_untimed(formula.local_time):
        label1 = Label(singleton(formula.child), singleton(), singleton(), singleton())
        label2 = Label(singleton(), singleton(formula), singleton(), singleton())
        return {label1, label2}
    else:
        if formula not in ctx:
            cur, interval, f = Partition(depth), formula.local_time, formula.child

            t_pre = TimePreFinally(cur, interval)
            t_in = TimeIntersectFinally(cur, interval)
            f1, f2 = FinallyUp(cur, interval, f), FinallyUpIntersect(cur, interval, f)
            f3, f4 = FinallyUpDown(cur, cur, interval, f), FinallyUpIntersectDown(cur, cur, interval, f)

            label1 = Label(singleton(f1, t_pre), singleton(), singleton(), singleton())
            label2 = Label(singleton(f2, f, t_in), singleton(), singleton(), singleton())
            label3 = Label(singleton(f3, t_pre), singleton(), singleton(), singleton())
            label4 = Label(singleton(f4, f, t_in), singleton(), singleton(), singleton())

            return {label1, label2, label3, label4}
        else:
            return {empty_label()}


@_label_expand.register(FinallyUp)
def _(formula: FinallyUp, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    f, base, nxt_interval, interval = formula.child, formula.i, Partition(depth + 1), formula.interval
    t_pre = TimePreFinally(base, interval)
    t_in = TimeIntersectFinally(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1, f2 = FinallyUp(base, interval, f), FinallyUpIntersect(base, interval, f)
    f3, f4 = FinallyUpDown(base, nxt_interval, interval, f), FinallyUpIntersectDown(base, nxt_interval, interval, f)
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

    f1 = FinallyUpIntersectDown(base, end, interval, f)
    label1 = Label(singleton(), singleton(t_pre, formula), singleton(nxt), singleton())
    label2 = Label(singleton(), singleton(f, t_in, f1), singleton(nxt), singleton())

    return {label1, label2}


@_label_expand.register(FinallyUpIntersect)
def _(formula: FinallyUpIntersect, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    base, cur, f, interval = formula.i, Partition(depth), formula.child, formula.interval
    nxt_interval = Partition(depth + 1)
    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    nxt = FinallyFormula(interval, g, f)
    t_in = TimeIntersectFinally(base, interval)

    f1 = FinallyUp(cur - interval, interval, f)
    f2 = FinallyUpIntersectDown(base, nxt_interval, interval, f)
    f3 = FinallyUpDown(cur - interval, nxt_interval, interval, f)

    label1 = Label(singleton(), singleton(f, formula, t_in), singleton(), singleton(nxt))
    label2 = Label(singleton(), singleton(f1, _nnf(f, threshold)), singleton(), singleton(nxt))
    label3 = Label(singleton(), singleton(f2, f, t_in), singleton(), singleton(nxt))
    label4 = Label(singleton(), singleton(f3, _nnf(f, threshold)), singleton(), singleton(nxt))

    return {label1, label2, label3, label4}


@_label_expand.register(FinallyUpIntersectDown)
def _(formula: FinallyUpIntersectDown, ctx: Set[Formula], depth: int, threshold: float) -> Set[Label]:
    base, end, f, interval = formula.i, formula.k, formula.child, formula.interval
    cur = Partition(depth)
    lst = TimePostFinally(end, interval)
    t_in = TimeIntersectFinally(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    nxt = FinallyFormula(interval, g, f)

    f1 = FinallyUpDown(cur - interval, end, interval, f)

    label1 = Label(singleton(lst), singleton(), singleton(nxt), singleton())
    label2 = Label(singleton(), singleton(formula, f, t_in), singleton(nxt), singleton())
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


def _remove_invalid_label(labels: Set[Label]) -> Set[Label]:
    n_labels = set()
    for lb in labels:
        f, a = lb.forbidden, lb.assertion
        if not lb.nxt.intersection(f) and a.issubset(lb.nxt):
            n_labels.add(lb)
    return n_labels


def _remove_unreachable(labels: Set[Label]) -> Set[Label]:
    n_labels = set()
    for lb in labels:
        c, n = lb.cur, lb.nxt
        c = set(filter(lambda x: isinstance(x, TimeLast), c))
        # time last cannot have next states
        if len(c) > 0 and len(n) > 0:
            continue

        n_labels.add(lb)
    return n_labels


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
    cur = Partition(depth)
    return cur.sup() >= tau_max()


@_time_translate.register(TimeIntersect)
def _(formula: TimeIntersect, depth: int) -> Formula:
    cur = Partition(depth)
    return And([cur.inf() <= formula.i.inf() + inf(formula.interval),
                formula.i.inf() + inf(formula.interval) <= cur.sup()])


@_time_translate.register(TimePre)
def _(formula: TimePre, depth: int) -> Formula:
    cur = Partition(depth)
    return cur.sup() <= formula.i.inf() + inf(formula.interval)


@_time_translate.register(TimePost)
def _(formula: TimePost, depth: int) -> Formula:
    cur = Partition(depth)
    return And([cur.inf() <= formula.i.sup() + sup(formula.interval),
                formula.i.sup() + sup(formula.interval) <= cur.sup()])


@_time_translate.register(TimeNotPost)
def _(formula: TimeNotPost, depth: int) -> Formula:
    cur = Partition(depth)
    return cur.sup() <= formula.i.sup() + sup(formula.interval)


@_time_translate.register(TimePreFinally)
def _(formula: TimePreFinally, depth: int) -> Formula:
    base, cur, interval = formula.i, Partition(depth), formula.interval
    return (cur.inf() - sup(interval)) <= base.inf()


@_time_translate.register(TimeIntersectFinally)
def _(formula: TimeIntersectFinally, depth: int) -> Formula:
    base, cur, interval = formula.i, Partition(depth), formula.interval
    c_inf, c_sup = cur.inf() - sup(interval), cur.sup() - inf(interval)
    return And([c_inf <= base.inf(), base.inf() <= c_sup])


@_time_translate.register(TimePostFinally)
def _(formula: TimePostFinally, depth: int) -> Formula:
    base, cur, interval = formula.i, Partition(depth), formula.interval
    c_inf, c_sup = cur.inf() - sup(interval), cur.sup() - inf(interval)
    return And([c_inf <= base.sup(), base.sup() <= c_sup])


def split_label(label: Label) -> Tuple[Set[Formula], Set[Formula]]:
    non_intermediate, intermediate = set(), set()
    for lb in label.cur:
        if isinstance(lb, Proposition):
            non_intermediate.add(lb)
        else:
            intermediate.add(lb)
    return non_intermediate, intermediate


def is_untimed(interval: Interval):
    untimed = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    return interval == untimed


def _nnf(formula: Formula, threshold: float):
    f = strengthening(formula, threshold)
    return reduce_not(Not(f))
