import abc
from functools import singledispatch, reduce
from itertools import product
from typing import Dict, Tuple, Set, List, Iterable, FrozenSet, Union

from ...smt.goal.aux import *
from ....constraints.aux.operations import Substitution, VarSubstitution
from ....constraints.constraints import *

Label = FrozenSet[Bool]
LabelSet = Set[Label]


@singledispatch
def init(formula: Formula) -> LabelSet:
    raise Exception("cannot find a matching rule ({})".format(formula))


@init.register(Proposition)
def _(formula: Proposition) -> LabelSet:
    return singleton(chi(1, 1, formula))


@init.register(And)
def _(formula: And) -> LabelSet:
    return labels_product(*[init(c) for c in formula.children])


@init.register(Or)
def _(formula: Or) -> LabelSet:
    return labels_union(*[init(c) for c in formula.children])


@init.register(UntilFormula)
def _(formula: UntilFormula) -> LabelSet:
    left, right = init(formula.left), init(formula.right)
    prod1 = labels_product(left, right)
    prod2 = labels_product(left, singleton(chi(1, 1, formula)))

    return labels_union(prod1, prod2)


@init.register(ReleaseFormula)
def _(formula: ReleaseFormula) -> LabelSet:
    left, right = init(formula.left), init(formula.right)
    prod1 = labels_product(right, singleton(chi(1, 1, formula)))
    prod2 = labels_product(right, singleton(t_last(1)))

    return labels_union(left, prod1, prod2)


@init.register(FinallyFormula)
def _(formula: FinallyFormula) -> LabelSet:
    # untimed
    if is_untimed(formula.local_time):
        return labels_union(init(formula.child), singleton(chi(1, 1, formula)))
    else:
        # timed
        interval = Interval(True, RealVal("0.0"), formula.local_time.left, True)
        _init = init(GloballyFormula(interval, formula.global_time, formula.child))
        _prod = labels_product(_init, singleton(t_in(1, 1, formula.local_time)))
        return labels_union(_prod, singleton(chi(1, 1, formula)))


@init.register(GloballyFormula)
def _(formula: GloballyFormula) -> LabelSet:
    if is_untimed(formula.local_time):
        c0 = init(formula.child)
        c1 = labels_product(c0, singleton(chi(1, 1, formula)))
        c2 = labels_product(c0, singleton(t_last(1)))
        return labels_union(c1, c2)
    else:
        c1 = singleton(chi(1, 1, formula), t_pre(1, 1, formula.local_time))
        f = ValidGloballyFormula(formula.local_time, formula.global_time, formula.child)
        c2 = labels_product(init(formula.child), singleton(chi(1, 1, f)))
        return labels_union(c1, c2, singleton(t_post(1, 1, formula.local_time)))


def expand(label: Label, hash_dict) -> LabelSet:
    if len(label) > 0:
        return labels_product(*[_apply_next(lab, hash_dict) for lab in label])
    else:
        return singleton()


def split_label(label: Label, hash_dict: Dict[hash, Formula]) -> Tuple[Set[Bool], Set[Bool]]:
    ap = set()
    non_ap = set()
    for v in label:
        if is_time(v):
            ap.add(v)
        else:
            f = _get_chi_formula(v, hash_dict)
            if isinstance(f, Proposition):
                ap.add(v)
            else:
                non_ap.add(v)
    return ap, non_ap


def _apply_next(v: Bool, hash_dict):
    if not (is_chi(v) or is_time(v)):
        raise Exception("only goal variables allowed ({})".format(v))

    if is_time(v):
        return singleton()

    return _next(*_get_chi_info(v, hash_dict))


@singledispatch
def _next(formula: Formula, i: int, k: int):
    raise Exception("cannot find a matching rule ({})".format(formula))


@_next.register(Proposition)
def _(formula: Proposition, i: int, k: int):
    return singleton()


@_next.register(And)
def _(formula: And, i: int, k: int):
    return singleton()


@_next.register(Or)
def _(formula: Or, i: int, k: int):
    return singleton()


@_next.register(UntilFormula)
def _(formula: UntilFormula, i: int, k: int):
    assert i == k

    c1 = chi(i + 1, i + 1, formula.left)
    c2 = chi(i + 1, i + 1, formula.right)
    c3 = chi(i + 1, i + 1, formula)
    return {frozenset({c1, c2}), frozenset({c1, c3})}


@_next.register(ReleaseFormula)
def _(formula: ReleaseFormula, i: int, k: int):
    assert i == k

    c1 = chi(i + 1, i + 1, formula.left)
    c2 = chi(i + 1, i + 1, formula.right)
    c3 = chi(i + 1, i + 1, formula)
    c4 = t_last(i + 1)

    return {frozenset({c1}), frozenset({c2, c3}), frozenset({c2, c4})}


@_next.register(FinallyFormula)
def _(formula: FinallyFormula, i: int, k: int):
    if is_untimed(formula.local_time):
        assert i == k
        return {frozenset({chi(i + 1, k + 1, formula.child)}), frozenset({chi(i + 1, k + 1, formula)})}
    else:
        interval = Interval(True, RealVal("0.0"), formula.local_time.left, True)
        f = GloballyFormula(interval, formula.global_time, formula.child)

        c1 = chi(k + 1, k + 1, f)
        c2 = t_in(i, k + 1, formula.local_time)
        c3 = chi(i, k + 1, formula)

        return {frozenset({c1, c2}), frozenset({c3})}


@_next.register(GloballyFormula)
def _(formula: GloballyFormula, i: int, k: int):
    if is_untimed(formula.local_time):
        assert i == k
        c1 = chi(i + 1, k + 1, formula.child)
        c2 = chi(i + 1, k + 1, formula)
        return {frozenset({c1, c2}), frozenset({c1, t_last(k + 1)})}
    else:
        c1 = chi(i, k + 1, formula)
        c2 = t_pre(i, k + 1, formula.local_time)
        c3 = chi(k + 1, k + 1, formula.child)
        c4 = chi(i, k + 1, formula)
        c5 = t_post(i, k + 1, formula.local_time)

        return {frozenset({c1, c2}), frozenset({c3, c4}), frozenset({c5})}


@_next.register(ValidGloballyFormula)
def _(formula: ValidGloballyFormula, i: int, k: int):
    f = ValidGloballyFormula(formula.local_time, formula.global_time, formula.child)

    c1 = chi(k + 1, k + 1, formula.child)
    c2 = chi(i, k + 1, f)
    c3 = t_post(i, k + 1, formula.local_time)
    c4 = t_last(k + 1)

    return {frozenset({c1, c2}), frozenset({c1, c3}), frozenset({c1, c4})}


def labels_product(*labels):
    return reduce(_labels_product, labels)


def labels_union(*labels):
    return reduce(_labels_union, labels)


def _labels_product(left: LabelSet, right: LabelSet):
    labels = set()
    for l1, l2 in set(product(left, right)):
        labels.add(frozenset(l1.union(l2)))
    return labels


def _labels_union(left: LabelSet, right: LabelSet):
    return left.union(right)


def singleton(*chi_s):
    return {frozenset(chi_s)}


def is_untimed(interval: Interval):
    untimed = Interval(True, RealVal("0.0"), RealVal("inf"), False)
    return interval == untimed


def t_pre(i: int, k: int, interval: Interval):
    return Bool("@time${}^{{{},{}}}_pre".format(hash(interval), i, k))


def t_post(i: int, k: int, interval: Interval):
    return Bool("@time${}^{{{},{}}}_post".format(hash(interval), i, k))


def t_last(index: int):
    return Bool("@time$0000^{}_last".format(index))


def t_in(i: int, k: int, interval: Interval):
    return Bool("@time${}^{{{},{}}}_in".format(hash(interval), i, k))


def is_time(v: Variable):
    return isinstance(v, Bool) and "@time" in v.id


def is_post_time(v: Variable):
    return is_time(v) and "_post" in v.id


def update_sub_formula(formulas: Set[Formula]):
    # TODO
    new_globally_formula: Set[ValidGloballyFormula] = set()
    for f in formulas:
        if isinstance(f, GloballyFormula) and not is_untimed(f.local_time):
            new_globally_formula.add(ValidGloballyFormula(f.local_time, f.global_time, f.child))

    formulas.update(new_globally_formula)


def translate(props: Set[Bool], tau_subst: VarSubstitution,
              hash_dict1: Dict[hash, Formula], hash_dict2: Dict[hash, Interval]) -> Set[Formula]:
    f_set: Set[Formula] = set()
    for prop in props:
        if is_chi(prop):
            f_set.add(_get_chi_formula(prop, hash_dict1))
        elif is_time(prop):
            f = _get_time_formula(prop, hash_dict2)
            f_set.add(tau_subst.substitute(f))
            # print("translate: {} to {}".format(prop, f))
        else:
            raise Exception("fail to translate a proposition {}".format(prop))
    return f_set


# v_id^{i, k}_{hash}
def _get_chi_info(v: Bool, hash_dict: Dict[hash, Formula]) -> Tuple[Formula, int, int]:
    assert is_chi(v)

    split = v.id.split("^")[1].split("_")
    hash_id = int(split[1])
    i, k = _index_info(split[0])

    if hash_id in hash_dict:
        return hash_dict[hash_id], i, k

    raise Exception("cannot find corresponding formula")


def _get_chi_formula(v: Bool, hash_dict: Dict[hash, Formula]) -> Formula:
    f, _, _ = _get_chi_info(v, hash_dict)
    return f


# @time${hash}^{i, k}_{type} or @time${hash}^{}_last
def _get_time_formula(v: Bool, hash_dict: Dict[hash, Interval]) -> Formula:
    assert is_time(v)
    split = v.id.split("^")
    hash_id, (indices, ty) = int(split[0].split("$")[1]), split[1].split("_")

    i, k = _index_info(indices)

    if ty == "last":
        assert i == k
        return symbolic_sup(i) == tau_max()
    else:
        p_i, p_k = _partition(i), _partition(k)
        if hash_id in hash_dict:
            interval = hash_dict[hash_id]
            if ty == "in":
                l_interval = p_k - interval
                r_interval = Interval(p_k.left_end, p_k.left, tau_max(), True) - interval

                l_c = _2formula(l_interval.left, l_interval.left_end, p_i.left, p_i.left_end)
                r_c = _2formula(p_i.right, p_i.right_end, r_interval.right, r_interval.right_end)
                return And([l_c, r_c])
            elif ty == "pre":
                t_interval = p_i + interval
                return _2formula(p_k.right, p_k.right_end, t_interval.left, t_interval.left_end)
            elif ty == "post":
                t_interval = p_i + interval
                return And([t_interval.right == p_k.right, BoolVal(str(t_interval.right_end == p_k.right_end))])
            else:
                raise Exception("wrong type of time variable ({})".format(ty))
        else:
            raise Exception("cannot find corresponding interval")


def _index_info(index_str: str) -> Tuple[int, int]:
    index_str = index_str.replace("{", "").replace("}", "")
    # {i, k}
    if "," in index_str:
        ik_str = index_str.split(",")

        assert len(ik_str) == 2
        i, k = int(ik_str[0]), int(ik_str[1])
    else:
        i, k = int(index_str), int(index_str)

    return i, k


def _partition(index: int) -> Interval:
    # open
    if index % 2 == 0:
        return Interval(False, symbolic_inf(index), symbolic_sup(index), False)
    else:
        return Interval(True, symbolic_inf(index), symbolic_sup(index), True)


def _2formula(left: Union[Real, RealVal], is_close1,
              right: Union[Real, RealVal], is_close2) -> Formula:
    is_close = is_close1 and is_close2
    if is_close:
        return left < right
    else:
        return left <= right


def tau_max():
    return Real("tau_max")
