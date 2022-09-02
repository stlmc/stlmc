from functools import singledispatch, reduce
from itertools import product
from typing import Dict, Tuple, Set, FrozenSet

from .label import *
from ....constraints.constraints import *

Labels = FrozenSet[Label]
LabelInfo = Tuple[int, int, Formula]


class ValidGloballyFormula(UnaryTemporalFormula):
    def __init__(self, local_time: Interval, global_time: Interval, child: Formula):
        UnaryTemporalFormula.__init__(self, local_time, global_time, child, "validGlobally", "[*]")


def init(labels: Labels, cache1: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    if len(labels) > 0:
        return canonicalize(labels_product(*[_apply_current(label, cache1) for label in labels]))
    else:
        return singleton()


def expand(labels: Labels, cache1: Dict[LabelInfo, Set[Labels]],
           cache2: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    if len(labels) > 0:
        return canonicalize(labels_product(*[_apply_next(label, cache1, cache2) for label in labels]))
    else:
        return singleton()


def _apply_next(label: Label, cache1: Dict[LabelInfo, Set[Labels]],
                cache2: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    if isinstance(label, Chi):
        if not label.is_intermediate():
            return singleton()

    if isinstance(label, TimeLabel):
        return singleton()

    nxt_labels = _next(label.formula, label.i, label.k, cache2)
    return labels_union(*[labels_product(*[_apply_current(lab, cache1) for lab in labels]) for labels in nxt_labels])


@singledispatch
def _next(formula: Formula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    raise Exception("cannot find a matching rule ({})".format(formula))


@_next.register(Proposition)
def _(formula: Proposition, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    return singleton()


@_next.register(And)
def _(formula: And, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    return singleton()


@_next.register(Or)
def _(formula: Or, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    return singleton()


@_next.register(UntilFormula)
def _(formula: UntilFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    assert i == k

    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        c1 = Chi(i + 1, i + 1, formula.left)
        c2 = Chi(i + 1, i + 1, formula.right)
        c3 = Chi(i + 1, i + 1, formula)

        cache[label_info] = {frozenset({c1, c2}), frozenset({c1, c3})}
        return cache[label_info]


@_next.register(ReleaseFormula)
def _(formula: ReleaseFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    assert i == k

    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        c1 = Chi(i + 1, i + 1, formula.left)
        c2 = Chi(i + 1, i + 1, formula.right)
        c3 = Chi(i + 1, i + 1, formula)
        c4 = TimeLast(i + 1)

        cache[label_info] = {frozenset({c1}), frozenset({c2, c3}), frozenset({c2, c4})}
        return cache[label_info]


@_next.register(FinallyFormula)
def _(formula: FinallyFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        if is_untimed(formula.local_time):
            assert i == k
            cache[label_info] = {frozenset({Chi(i + 1, k + 1, formula.child)}), frozenset({Chi(i + 1, k + 1, formula)})}
        else:
            interval = Interval(True, RealVal("0.0"), formula.local_time.left, True)
            f = GloballyFormula(interval, formula.global_time, formula.child)

            c1 = Chi(i, k + 1, f)
            c2 = TimeIn(i, k + 1, formula.local_time)
            c3 = Chi(i, k + 1, formula)

            cache[label_info] = {frozenset({c1, c2}), frozenset({c3})}

        return cache[label_info]


@_next.register(GloballyFormula)
def _(formula: GloballyFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        if is_untimed(formula.local_time):
            assert i == k
            c1 = Chi(i + 1, k + 1, formula.child)
            c2 = Chi(i + 1, k + 1, formula)
            cache[label_info] = {frozenset({c1, c2}), frozenset({c1, TimeLast(k + 1)})}
        else:
            f = ValidGloballyFormula(formula.local_time, formula.global_time, formula.child)

            c1 = TimePre(i, k + 1, formula.local_time)
            c2 = Chi(i, k + 1, formula)
            c3 = Chi(k + 1, k + 1, formula.child)
            c4 = Chi(i, k + 1, f)
            c5 = TimeLast(k + 1)

            cache[label_info] = {frozenset({c1, c2}), frozenset({c3, c4}), frozenset({c1, c5})}
        return cache[label_info]


@_next.register(ValidGloballyFormula)
def _(formula: ValidGloballyFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        c1 = Chi(k + 1, k + 1, formula.child)
        c2 = Chi(i, k + 1, formula)
        c3 = TimePost(i, k + 1, formula.local_time)
        c4 = TimeLast(k + 1)

        cache[label_info] = {frozenset({c1, c2}), frozenset({c1, c3}), frozenset({c1, c4})}
        return cache[label_info]


def _apply_current(label: Label, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    if isinstance(label, Chi):
        if not label.is_intermediate():
            return singleton(label)

    if isinstance(label, TimeLabel):
        return singleton(label)

    return _current(label.formula, label.i, label.k, cache)


@singledispatch
def _current(formula: Formula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    raise Exception("cannot find a matching rule1 ({})".format(formula))


@_current.register(Proposition)
def _(formula: Proposition, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    assert i == k

    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        cache[label_info] = singleton(Chi(*label_info))
        return cache[label_info]


@_current.register(And)
def _(formula: And, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    assert i == k

    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        cache[label_info] = labels_product(*[_current(c, i, k, cache) for c in formula.children])
        return cache[label_info]


@_current.register(Or)
def _(formula: Or, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    assert i == k

    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        cache[label_info] = labels_union(*[_current(c, i, k, cache) for c in formula.children])
        return cache[label_info]


@_current.register(UntilFormula)
def _(formula: UntilFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    assert is_untimed(formula.local_time) and i == k

    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:

        left, right = _current(formula.left, i, k, cache), _current(formula.right, i, k, cache)
        prod1 = labels_product(left, right)
        prod2 = labels_product(left, singleton(Chi(i, k, formula)))

        cache[label_info] = labels_union(prod1, prod2)

        return cache[label_info]


@_current.register(ReleaseFormula)
def _(formula: ReleaseFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    assert is_untimed(formula.local_time) and i == k

    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:

        left, right = _current(formula.left, i, k, cache), _current(formula.right, i, k, cache)
        prod1 = labels_product(right, singleton(Chi(i, k, formula)))
        prod2 = labels_product(right, singleton(TimeLast(i)))

        cache[label_info] = labels_union(left, prod1, prod2)
        return cache[label_info]


@_current.register(FinallyFormula)
def _(formula: FinallyFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:

        # untimed
        if is_untimed(formula.local_time):
            assert i == k
            cache[label_info] = labels_union(_current(formula.child, i, k, cache), singleton(Chi(i, k, formula)))
        else:
            # timed
            interval = Interval(True, RealVal("0.0"), formula.local_time.left, True)
            left = _current(GloballyFormula(interval, formula.global_time, formula.child), i, k, cache)
            prod = labels_product(left, singleton(TimeIn(i, k, formula.local_time)))
            cache[label_info] = labels_union(prod, singleton(Chi(i, k, formula)))

        return cache[label_info]


@_current.register(GloballyFormula)
def _(formula: GloballyFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        if is_untimed(formula.local_time):
            assert i == k
            c0 = _current(formula.child, i, k, cache)
            c1 = labels_product(c0, singleton(Chi(i, k, formula)))
            c2 = labels_product(c0, singleton(TimeLast(i)))
            cache[label_info] = labels_union(c1, c2)
        else:
            pre = TimePre(i, k, formula.local_time)
            f = ValidGloballyFormula(formula.local_time, formula.global_time, formula.child)

            c1 = singleton(pre, Chi(i, k, formula))
            c2 = singleton(pre, TimeLast(k))
            c3 = labels_product(_current(formula.child, k, k, cache), _current(f, i, k, cache))
            cache[label_info] = labels_union(c1, c2, c3)

        return cache[label_info]


@_current.register(ValidGloballyFormula)
def _(formula: ValidGloballyFormula, i: int, k: int, cache: Dict[LabelInfo, Set[Labels]]) -> Set[Labels]:
    label_info = (i, k, formula)

    if label_info in cache:
        return cache[label_info]
    else:
        c1 = _current(formula.child, k, k, cache)

        prod1 = labels_product(c1, singleton(TimeLast(k)))
        prod2 = labels_product(c1, singleton(Chi(i, k, formula)))
        prod3 = labels_product(c1, singleton(TimePost(i, k, formula.local_time)))

        cache[label_info] = labels_union(prod1, prod2, prod3)
        return cache[label_info]


def canonicalize(labels_set: Set[Labels]):
    labels_s = set(filter(lambda x: len(x) > 0, labels_set))
    subsume: Dict[Labels, Set[Labels]] = dict()
    pre_status: Dict[Labels, Set[Labels]] = dict()
    while True:
        _calc_label_subsume(labels_s, subsume)

        cur_status = subsume
        if cur_status == pre_status:
            break

        pre_status = subsume.copy()

    # ignore self
    for labels in subsume:
        subsume[labels].discard(labels)

    removed = set()
    for labels in labels_s:
        assert labels in subsume
        if len(subsume[labels]) > 0:
            removed.add(labels)

    return labels_s.difference(removed)


def _calc_label_subsume(labels_set: Set[Labels], subsume: Dict[Labels, Set[Labels]]):
    def _add_to_dict(_k: Labels, *_vs):
        if _k not in subsume:
            subsume[_k] = {_v for _v in _vs}
        else:
            for _v in _vs:
                subsume[_k].add(_v)

    for labels in labels_set:
        waiting = labels_set.copy()
        while len(waiting) > 0:
            n = waiting.pop()
            if _labels_subsume(labels, n):
                _add_to_dict(labels, n)
                if n in subsume:
                    _add_to_dict(labels, *subsume[n])
                    waiting.difference_update(subsume[n])


def _labels_subsume(labels1: Labels, labels2: Labels) -> bool:
    for label in labels2:
        if label not in labels1:
            return False
    return True


def labels_product(*labels):
    return reduce(_labels_product, labels)


def labels_union(*labels):
    return reduce(_labels_union, labels)


def _labels_product(left: Set[Labels], right: Set[Labels]):
    labels = set()
    for l1, l2 in set(product(left, right)):
        labels.add(frozenset(l1.union(l2)))
    return labels


def _labels_union(left: Set[Labels], right: Set[Labels]):
    return left.union(right)


def singleton(*labels) -> Set[Labels]:
    return {frozenset(labels)}


def is_untimed(interval: Interval):
    untimed = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    return interval == untimed


def is_timed_label(label: Label):
    return isinstance(label, TimeLabel)


def is_post_time(label: Label):
    return isinstance(label, TimePost)


def update_sub_formula(formulas: Set[Formula]):
    # TODO
    new_globally_formula: Set[ValidGloballyFormula] = set()
    for f in formulas:
        if isinstance(f, GloballyFormula) and not is_untimed(f.local_time):
            new_globally_formula.add(ValidGloballyFormula(f.local_time, f.global_time, f.child))

    formulas.update(new_globally_formula)


def translate(label: Label) -> Formula:
    if isinstance(label, Chi):
        return label.formula
    elif isinstance(label, TimeLabel):
        return _get_time_formula(label)
    else:
        raise Exception("fail to translate a label ({})".format(label))


def _get_time_formula(label: Label) -> Formula:
    assert isinstance(label, TimeLabel)

    if isinstance(label, TimeLast):
        assert label.i == label.k
        return partition_sup(label.i) == tau_max()
    elif isinstance(label, TimeIn):
        l_c = partition_inf(label.k) - label.interval.right <= partition_inf(label.i)
        r_c = partition_sup(label.i) <= tau_max()
        return And([l_c, r_c])
    elif isinstance(label, TimePre):
        return partition_sup(label.k) <= partition_inf(label.i) + label.interval.left
    elif isinstance(label, TimePost):
        return partition_sup(label.i) + label.interval.right == partition_sup(label.k)
    else:
        raise Exception("wrong type of time label")


def partition_sup(index: int):
    return Real("tau_{}".format(index))


def partition_inf(index: int):
    return Real("tau_{}".format(index - 1))


def tau_max():
    return Real("tau_max")


def split_label(labels: Labels) -> Tuple[Labels, Labels]:
    non_intermediate, intermediate = set(), set()
    for label in labels:
        if isinstance(label, TimeLabel):
            non_intermediate.add(label)
        else:
            if isinstance(label, Chi):
                if label.is_intermediate():
                    intermediate.add(label)
                else:
                    non_intermediate.add(label)
            else:
                raise Exception("unknown label type")
    return frozenset(non_intermediate), frozenset(intermediate)
