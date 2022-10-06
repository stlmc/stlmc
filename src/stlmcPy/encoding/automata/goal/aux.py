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

        update_queue = update_waiting_list(p_f, lbs, (p_c, p_l))
        update_queue = _remove_invalid_label(update_queue)
        update_queue = _remove_unreachable(update_queue)

        waiting_list.extend(update_queue)

    # print("# iteration {}".format(loop))
    return labels


def init(formula: Formula, cache: Dict[Label, Set[Label]]):
    s_label = Label(singleton(), singleton(formula), singleton(), singleton())
    return expand(s_label, 1, cache)


@singledispatch
def _label_expand(formula: Formula, ctx: Set[Formula], depth: int) -> Set[Label]:
    raise Exception("cannot find a matching rule ({})".format(formula))


@_label_expand.register(Proposition)
def _(formula: Proposition, ctx: Set[Formula], depth: int) -> Set[Label]:
    return {Label(singleton(), singleton(), singleton(), singleton())}


@_label_expand.register(GloballyFormula)
def _(formula: GloballyFormula, ctx: Set[Formula], depth: int) -> Set[Label]:
    if formula not in ctx:
        if is_untimed(formula.local_time):
            pass
        else:
            f, start, interval = formula.child, symbolic_interval(depth), formula.local_time

            f1, f2 = GloballyUp(start, interval, f), GloballyUpIntersect(interval, f)
            t_pre = TimePre(start, interval)
            # t_in = TimeIntersect(start, interval)

            lb1 = Label(singleton(f1, t_pre), singleton(), singleton(), singleton())
            # lb2 = Label(singleton(f2, t_in), singleton(), singleton(), singleton())
            lb2 = Label(singleton(f2), singleton(), singleton(), singleton())
            return {lb1, lb2}
    else:
        return {empty_label()}


@_label_expand.register(GloballyUp)
def _(formula: GloballyUp, ctx: Set[Formula], depth: int) -> Set[Label]:
    f, base, end, interval = formula.child, formula.i, symbolic_interval(depth), formula.interval
    pre = TimePre(base, interval)
    # its = TimeIntersect(base, interval)

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUpDown(base, end, interval, f)
    f2 = GloballyUpIntersect(interval, f)
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(f1), singleton(), singleton(nxt), singleton())
    label2 = Label(singleton(), singleton(formula, pre), singleton(), singleton(nxt))
    # label3 = Label(singleton(), singleton(f2, its), singleton(), singleton(nxt))
    label3 = Label(singleton(), singleton(f2), singleton(), singleton(nxt))
    return {label1, label2, label3}


@_label_expand.register(GloballyUpDown)
def _(formula: GloballyUpDown, ctx: Set[Formula], depth: int) -> Set[Label]:
    f = formula.child
    base, end, cur, interval = formula.i, formula.k, symbolic_interval(depth), formula.interval

    pre = TimePre(end, interval)
    tls = TimeLast()
    # its = TimeIntersect(end, interval)

    f1 = GloballyUpIntersectDown(end, interval, f)

    # label1 = Label(singleton(), singleton(f1, its), singleton(), singleton())
    label1 = Label(singleton(), singleton(f1), singleton(), singleton())
    label2 = Label(singleton(), singleton(formula, pre), singleton(), singleton())
    label3 = Label(singleton(tls), singleton(), singleton(), singleton())

    return {label1, label2, label3}


@_label_expand.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect, ctx: Set[Formula], depth: int) -> Set[Label]:
    f, end, interval = formula.child, symbolic_interval(depth), formula.interval

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUpIntersectDown(end, interval, f)
    f2 = GloballyFormula(interval, g, f)

    label1 = Label(singleton(f1), singleton(), singleton(f2), singleton())
    label2 = Label(singleton(f), singleton(formula), singleton(), singleton(f2))

    return {label1, label2}


@_label_expand.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown, ctx: Set[Formula], depth: int) -> Set[Label]:
    f, end, current, interval = formula.child, formula.i, symbolic_interval(depth), formula.interval

    tps = TimePost(end, interval)
    # n_tps = TimeNotPost(end, interval)
    tls = TimeLast()

    label1 = Label(singleton(tps, f), singleton(), singleton(), singleton())
    label2 = Label(singleton(tls, f), singleton(), singleton(), singleton())
    label3 = Label(singleton(f), singleton(formula), singleton(), singleton())

    return {label1, label2, label3}


@_label_expand.register(FinallyFormula)
def _(formula: FinallyFormula, ctx: Set[Formula], depth: int) -> Set[Label]:
    if is_untimed(formula.local_time):
        label1 = Label(singleton(formula.child), singleton(), singleton(), singleton())
        label2 = Label(singleton(), singleton(formula), singleton(), singleton())
        return {label1, label2}
    else:
        if formula not in ctx:
            cur, interval, f = symbolic_interval(depth), formula.local_time, formula.child
            f1 = FinallyUp(cur, interval, f)
            f2 = FinallyUpIntersect(interval, f)

            label1 = Label(singleton(f1, TimePre(cur, interval)), singleton(), singleton(), singleton())
            label2 = Label(singleton(f2, f, TimeIntersect(cur, interval)), singleton(), singleton(), singleton())

            return {label1, label2}
        else:
            return {empty_label()}


@_label_expand.register(FinallyUp)
def _(formula: FinallyUp, ctx: Set[Formula], depth: int) -> Set[Label]:
    label1 = FinallyUp


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
    l_n, r_n = 2 * num - 2, 2 * num - 1
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
        if isinstance(lb_f, TimeProposition):
            f_s.add(_time_translate(lb_f, depth))
        elif isinstance(lb_f, Proposition):
            f_s.add(lb_f)
        else:
            raise Exception("fail to translate a label ({})".format(label))
    return f_s, intermediate


def _time_translate(time_f: TimeProposition, depth: int) -> Formula:
    assert isinstance(time_f, TimeProposition)
    cur = symbolic_interval(depth)

    if isinstance(time_f, TimeLast):
        return sup(cur) >= tau_max()
    elif isinstance(time_f, TimeIntersect):
        return And([inf(cur) <= inf(time_f.i) + inf(time_f.interval),
                    inf(time_f.i) + inf(time_f.interval) <= sup(cur)])
    elif isinstance(time_f, TimePre):
        return sup(cur) <= inf(time_f.i) + inf(time_f.interval)
    elif isinstance(time_f, TimePost):
        return And([inf(cur) <= sup(time_f.i) + sup(time_f.interval),
                    sup(time_f.i) + sup(time_f.interval) <= sup(cur)])
    elif isinstance(time_f, TimeNotPost):
        return sup(cur) <= sup(time_f.i) + sup(time_f.interval)
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


def stuttering(label: Label, labels: Set[Label], depth: int) -> Set[Label]:
    removed = set()
    for lb in labels:
        if _stuttering_equal(label, lb):
            removed.add(lb)
    return labels.difference(removed)


def _stuttering_equal(label1: Label, label2: Label):
    return label1.cur == label2.cur


def is_untimed(interval: Interval):
    untimed = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    return interval == untimed

# def _stuttering_time_equal(f1: TimeProposition, f2: TimeProposition) -> bool:
#     assert isinstance(f1, TimeProposition) and isinstance(f2, TimeProposition)
#
#     is_eq = f1.i == f2.i and f1.interval == f2.interval
#     ty_eq = any([isinstance(f1, TimeLast) and isinstance(f2, TimeLast),
#                  isinstance(f1, TimeIntersect) and isinstance(f2, TimeIntersect),
#                  isinstance(f1, TimePre) and isinstance(f2, TimePre),
#                  isinstance(f1, TimePost) and isinstance(f2, TimePost),
#                  isinstance(f1, TimeNotPost) and isinstance(f2, TimeNotPost)])
#
#     return is_eq and ty_eq
