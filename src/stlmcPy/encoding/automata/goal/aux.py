from functools import singledispatch
from itertools import product
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
            lb = Label(singleton(formula.child), singleton(formula), singleton(), singleton())
            return {lb}
        else:
            f, start, interval = formula.child, symbolic_interval(depth), formula.local_time

            f1, f2 = GloballyUp(start, interval, f), GloballyUpIntersect(interval, f)
            f3, f4 = GloballyUpDown(start, start, interval, f), GloballyUpIntersectDown(start, interval, f)
            t_pre = TimePre(start, interval)
            t_in = TimeIntersect(start, interval)

            g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
            nxt = GloballyFormula(interval, g, f)

            lb1 = Label(singleton(f1, t_pre), singleton(), singleton(), singleton(nxt))
            lb2 = Label(singleton(f2, t_in), singleton(), singleton(), singleton(nxt))
            lb3 = Label(singleton(f3, t_pre), singleton(), singleton(nxt), singleton())
            lb4 = Label(singleton(f4, t_in), singleton(), singleton(nxt), singleton())
            return {lb1, lb2, lb3, lb4}
    else:
        return {empty_label()}


@_label_expand.register(GloballyUp)
def _(formula: GloballyUp, ctx: Set[Formula], depth: int) -> Set[Label]:
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
    label3 = Label(singleton(), singleton(f3, pre), singleton(nxt), singleton())
    label4 = Label(singleton(), singleton(f4, its), singleton(nxt), singleton())
    return {label1, label2, label3, label4}


@_label_expand.register(GloballyUpDown)
def _(formula: GloballyUpDown, ctx: Set[Formula], depth: int) -> Set[Label]:
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
def _(formula: GloballyUpIntersect, ctx: Set[Formula], depth: int) -> Set[Label]:
    f, end, interval = formula.child, symbolic_interval(depth), formula.interval

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    f1 = GloballyUpIntersectDown(end, interval, f)
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(), singleton(f1), singleton(nxt), singleton())
    label2 = Label(singleton(f), singleton(formula), singleton(), singleton(nxt))

    return {label1, label2}


@_label_expand.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown, ctx: Set[Formula], depth: int) -> Set[Label]:
    f, end, current, interval = formula.child, formula.i, symbolic_interval(depth), formula.interval

    g = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    tps = TimePost(end, interval)
    # n_tps = TimeNotPost(end, interval)
    tls = TimeLast()
    nxt = GloballyFormula(interval, g, f)

    label1 = Label(singleton(tps, f), singleton(), singleton(nxt), singleton())
    label2 = Label(singleton(tls, f), singleton(), singleton(nxt), singleton())
    label3 = Label(singleton(f), singleton(formula), singleton(), singleton(nxt))

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
        "up&down<>": lambda x: isinstance(x, GloballyUpDown),
        "up<*>down<>": lambda x: isinstance(x, GloballyUpIntersectDown)
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
                pair.update((f1, f2))

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
