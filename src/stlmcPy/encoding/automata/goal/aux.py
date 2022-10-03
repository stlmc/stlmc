from functools import singledispatch
from typing import Dict, List

from .label import *
from ....constraints.aux.operations import inf, sup
from ....constraints.constraints import *


def expand(label: Label, depth: int, cache: Dict[Label, Set[Label]]) -> Set[Label]:
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
        lbs = _label_expand(p_f, c, depth)

        update_queue = _apply_forbidden(update_waiting_list(p_f, lbs, (p_c, p_l)), f)
        waiting_list.extend(update_queue)

    print("# iteration {}".format(loop))
    return labels


def init(formula: Formula, cache: Dict[Label, Set[Label]]):
    s_label = Label(singleton(), singleton(formula), singleton())
    return expand(s_label, 1, cache)


@singledispatch
def _label_expand(formula: Formula, ctx: Set[Formula], depth: int) -> Set[Label]:
    raise Exception("cannot find a matching rule ({})".format(formula))


@_label_expand.register(Proposition)
def _(formula: Proposition, ctx: Set[Formula], depth: int) -> Set[Label]:
    return {Label(singleton(), singleton(), singleton())}


@_label_expand.register(GloballyFormula)
def _(formula: GloballyFormula, ctx: Set[Formula], depth: int) -> Set[Label]:
    if formula not in ctx:
        j_i, interval = symbolic_interval(depth), formula.local_time
        return {Label(singleton(GloballyUp(j_i, interval, formula.child)), singleton(), singleton())}
    else:
        return {Label(singleton(), singleton(), singleton())}


@_label_expand.register(GloballyUp)
def _(formula: GloballyUp, ctx: Set[Formula], depth: int) -> Set[Label]:
    f = formula.child
    j_i, j_k, interval = formula.i, symbolic_interval(depth), formula.interval
    pre = TimePre(j_i, j_k, interval)
    its = TimeIntersect(j_i, j_k, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyFormula(interval, g, f)
    f2 = GloballyUpIntersect(j_i, interval, f)

    label1 = Label(singleton(pre, GloballyUpDown(j_i, j_k, interval, f)), singleton(), singleton(f1))
    label2 = Label(singleton(pre), singleton(formula), singleton())
    label3 = Label(singleton(its, f), singleton(f2), singleton())

    return {label1, label2, label3}


@_label_expand.register(GloballyUpDown)
def _(formula: GloballyUpDown, ctx: Set[Formula], depth: int) -> Set[Label]:
    f = formula.child
    j_i, j_j, j_k, interval = formula.i, formula.k, symbolic_interval(depth), formula.interval

    pre = TimePre(j_i, j_k, interval)
    tls = TimeLast(j_k)
    its = TimeIntersect(j_i, j_k, interval)

    f1 = GloballyUpIntersectDown(j_j, interval, f)

    label1 = Label(singleton(its, f1), singleton(), singleton())
    label2 = Label(singleton(pre), singleton(formula), singleton())
    label3 = Label(singleton(pre, tls), singleton(), singleton())

    return {label1, label2, label3}


@_label_expand.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect, ctx: Set[Formula], depth: int) -> Set[Label]:
    f, j_k, interval = formula.child, symbolic_interval(depth), formula.interval

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUpIntersectDown(j_k, interval, f)
    f2 = GloballyFormula(interval, g, f)

    label1 = Label(singleton(f1), singleton(), singleton(f2))
    label2 = Label(singleton(f), singleton(formula), singleton())

    return {label1, label2}


@_label_expand.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown, ctx: Set[Formula], depth: int) -> Set[Label]:
    f, j_i, j_k, interval = formula.child, formula.i, symbolic_interval(depth), formula.interval

    # inf(j_k) <= sup(j_i) + sup(interval), sup(j_i) + sup(interval) <= sup(j_k)
    tps, n_tps = TimePost(j_i, j_k, interval), TimeNotPost(j_i, j_k, interval)
    tls = TimeLast(j_k)

    label1 = Label(singleton(tps, f), singleton(), singleton())
    label2 = Label(singleton(tls, f), singleton(), singleton())
    label3 = Label(singleton(n_tps, f), singleton(formula), singleton())

    return {label1, label2, label3}


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


def update_labels(formula: Formula, labels: Set[Label], label: Label) -> List[Tuple[Set[Formula], Label]]:
    return [(lb.cur, Label(label.cur.union({formula}), label.nxt.union(lb.nxt),
                           label.forbidden.union(lb.forbidden))) for lb in labels]


def empty_label() -> Label:
    return Label(singleton(), singleton(), singleton())


def singleton(*formulas) -> Set[Formula]:
    return set(formulas)


def intersection(interval1: Interval, interval2: Interval):
    return inf(interval1) <= sup(interval2), inf(interval2) <= sup(interval1)


def symbolic_interval(num: int):
    # [tau_{num - 1}, tau_{num})
    lv = Real("tau_{}".format(num - 1))
    rv = Real("tau_{}".format(num))
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


def translate(label: Label) -> Set[Formula]:
    non_intermediate, _ = split_label(label)
    f_s = set()
    for lb_f in non_intermediate:
        if isinstance(lb_f, TimeProposition):
            f_s.add(_time_translate(lb_f))
        elif isinstance(lb_f, Proposition):
            f_s.add(lb_f)
        else:
            raise Exception("fail to translate a label ({})".format(label))
    return f_s


def _time_translate(time_f: TimeProposition) -> Formula:
    assert isinstance(time_f, TimeProposition)

    if isinstance(time_f, TimeLast):
        return sup(time_f.i) >= tau_max()
    elif isinstance(time_f, TimeIntersect):
        return inf(time_f.i) + inf(time_f.interval) <= sup(time_f.k)
    elif isinstance(time_f, TimePre):
        return sup(time_f.k) <= inf(time_f.i) + inf(time_f.interval)
    elif isinstance(time_f, TimePost):
        return And([inf(time_f.k) <= sup(time_f.i) + sup(time_f.interval),
                    sup(time_f.i) + sup(time_f.interval) <= sup(time_f.k)])
    elif isinstance(time_f, TimeNotPost):
        return sup(time_f.k) <= sup(time_f.i) + sup(time_f.interval)
    else:
        raise Exception("wrong type of time label")


def split_label(label: Label) -> Tuple[Set[Formula], Set[Formula]]:
    non_intermediate, intermediate = set(), set()
    for lb in label.cur:
        if isinstance(lb, Proposition):
            non_intermediate.add(lb)
        else:
            intermediate.add(lb)
    return non_intermediate, intermediate
