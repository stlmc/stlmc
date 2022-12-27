from typing import Tuple, FrozenSet

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

    empty_label = Label(singleton(), label.transition_nxt, singleton(), singleton(), label.max_clock_index)
    # formula queue, label, forbidden, assertion
    waiting_list = [(label.state_nxt.copy(), empty_label)]

    while len(waiting_list) > 0:
        p_c, p_l = waiting_list.pop()
        if len(p_c) <= 0:
            if _invariant_checking(p_l):
                labels.add(p_l)
            continue

        p_f = p_c.pop()
        lbs = _expand_label(p_f, p_l, label)

        update_queue = update_waiting_list(p_f, lbs, (p_c, p_l))
        waiting_list.extend(update_queue)

    return labels


def _invariant_checking(label: Label) -> bool:
    # label invariants
    inv_s = [_valid_label_checking, _valid_time_bound,
             _valid_clock]

    for inv in inv_s:
        if not inv(label):
            return False

    return True


def _valid_label_checking(label: Label) -> bool:
    checking_f_s = [
        _require_globally_checking, _not_require_globally_checking,
        _require_finally_checking, _not_require_finally_checking,
    ]

    for c_f in checking_f_s:
        if not c_f(label):
            return False

    return True


def _require_globally_checking(label: Label) -> bool:
    g_ups = set(filter(lambda x: isinstance(x, GloballyUp) or isinstance(x, GloballyUpIntersect), label.cur))
    for g in g_ups:
        if _infer_temporal_formula(g) not in label.cur:
            return False

    return True


def _not_require_globally_checking(label: Label) -> bool:
    # find globally temporal formulas in the current goals
    g_cur = set(filter(lambda x: isinstance(x, GloballyFormula), label.cur))

    for g_f in g_cur:
        if len(_get_globally_up_downs(g_f, label.cur)) > 0:
            return False

    return True


def _require_finally_checking(label: Label) -> bool:
    f_ups = set(filter(lambda x: isinstance(x, FinallyUp) or isinstance(x, FinallyUpIntersect), label.cur))
    for f in f_ups:
        if _infer_temporal_formula(f) not in label.cur:
            return False

    return True


def _not_require_finally_checking(label: Label) -> bool:
    # find finally temporal formulas in the current goals
    f_cur = set(filter(lambda x: isinstance(x, FinallyFormula), label.cur))

    for f_f in f_cur:
        if len(_get_finally_up_downs(f_f, label.cur)) > 0:
            return False

    return True


def _get_globally_up_downs(base: Formula, goals: Set[Formula]) -> Set[Formula]:
    return set(filter(lambda x: _is_globally_up_down(x, base) or _is_globally_up_intersect_down(x, base), goals))


def _is_globally_up_down(f: Formula, base: Formula) -> bool:
    return isinstance(f, GloballyUpDown) and hash(_infer_temporal_formula(f)) == hash(base)


def _is_globally_up_intersect_down(f: Formula, base: Formula) -> bool:
    return isinstance(f, GloballyUpIntersectDown) and hash(_infer_temporal_formula(f)) == hash(base)


def _get_finally_up_downs(base: Formula, goals: Set[Formula]) -> Set[Formula]:
    return set(filter(lambda x: _is_finally_up_down(x, base) or _is_finally_up_intersect_down(x, base), goals))


def _is_finally_up_down(f: Formula, base: Formula) -> bool:
    return isinstance(f, FinallyUpDown) and hash(_infer_temporal_formula(f)) == hash(base)


def _is_finally_up_intersect_down(f: Formula, base: Formula) -> bool:
    return isinstance(f, FinallyUpIntersectDown) and hash(_infer_temporal_formula(f)) == hash(base)


def _expand_label(formula: Formula, label: Label, p_label: Label) -> Set[Tuple[FrozenSet[Formula], Label]]:
    rules = {
        "prop": [_expand_proposition],
        "boolean": [
            _expand_and,
            _expand_or_1, _expand_or_2
        ],
        "globally": [
            _expand_untimed_globally_1, _expand_untimed_globally_2,
            _expand_timed_globally_1, _expand_timed_globally_2,

            _expand_globally_up_1, _expand_globally_up_2, _expand_globally_up_3,
            _expand_globally_up_4, _expand_globally_up_5,

            _expand_globally_up_intersect_1, _expand_globally_up_intersect_2,
            _expand_globally_up_intersect_3,

            _expand_globally_up_down_1, _expand_globally_up_down_2, _expand_globally_up_down_3,

            _expand_globally_up_intersect_down_1, _expand_globally_up_intersect_down_2,
            _expand_globally_up_intersect_down_3
        ],
        "finally": [
            _expand_untimed_finally_1, _expand_untimed_finally_2,
            _expand_timed_finally_1, _expand_timed_finally_2,

            _expand_finally_up_1, _expand_finally_up_2, _expand_finally_up_3, _expand_finally_up_4,

            _expand_finally_up_intersect_1, _expand_finally_up_intersect_2, _expand_finally_up_intersect_3,
            _expand_finally_up_intersect_4, _expand_finally_up_intersect_5,

            _expand_finally_up_down_1, _expand_finally_up_down_2,

            _expand_finally_up_intersect_down_1, _expand_finally_up_intersect_down_2,
            _expand_finally_up_intersect_down_3, _expand_finally_up_intersect_down_4
        ],
        "until": [
            _expand_until_formula_1, _expand_until_formula_2
        ],
        "release": [
            _expand_release_formula_1, _expand_release_formula_2, _expand_release_formula_3
        ]
    }

    labels = set()

    # apply rules
    for category in rules:
        for rule in rules[category]:
            r = rule(formula, label, p_label)
            if r is not None:
                labels.add((frozenset(r.state_cur), r))

    # if there are no rules to be applied
    if len(labels) <= 0:
        return {(frozenset(), label)}
    else:
        return labels


def _expand_proposition(formula: Proposition, label: Label,
                        p_label: Label) -> Optional[Label]:
    if not isinstance(formula, Proposition):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(), singleton(),
               singleton(), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# [] p --> [] p
def _expand_untimed_globally_1(formula: GloballyFormula, label: Label,
                               p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyFormula):
        return None

    if not is_untimed(formula.local_time):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.child), singleton(),
               singleton(formula), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# [] p --> tb
def _expand_untimed_globally_2(formula: GloballyFormula, label: Label,
                               p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyFormula):
        return None

    if not is_untimed(formula.local_time):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.child), singleton(),
               singleton(), singleton(TimeBound()), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# []_I p --> up[]_I p
def _expand_timed_globally_1(formula: GloballyFormula, label: Label,
                             p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyFormula):
        return None

    if is_untimed(formula.local_time):
        return None

    pre_cond = [_non_redundant_goal(formula, p_label)]
    post_cond = []

    if not all(pre_cond):
        return None

    clk_index = label.max_clock_index + 1
    clk = fresh_clock(clk_index)
    r_clk = ClkReset(clk)

    ty = TypeVariable(clk.id)
    oc = OpenClose(ty)
    f = GloballyUp(clk, ty, formula.local_time, formula.child)

    lb = Label(singleton(f), singleton(oc, r_clk),
               singleton(), singleton(), clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# []_I p --> up[*]_I p
def _expand_timed_globally_2(formula: GloballyFormula, label: Label, p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyFormula):
        return None

    if is_untimed(formula.local_time):
        return None

    pre_cond = [_non_redundant_goal(formula, p_label)]
    post_cond = []

    if not all(pre_cond):
        return None

    clk_index = label.max_clock_index + 1
    clk = fresh_clock(clk_index)
    r_clk = ClkReset(clk)

    ty = TypeVariable(clk.id)
    oc = OpenClose(ty)
    f = GloballyUpIntersect(clk, ty, formula.local_time, formula.child)

    lb = Label(singleton(f), singleton(oc, r_clk),
               singleton(), singleton(), clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[]_I p --> up[]_I p
def _expand_globally_up_1(formula: GloballyUp, label: Label,
                          p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeGloballyPre(formula.clock, formula.type, formula.interval)
    lb = Label(singleton(), singleton(), singleton(formula),
               singleton(t_pre), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[]_I p --> up[*]_I p
def _expand_globally_up_2(formula: GloballyUp, label: Label, p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeGloballyPre(formula.clock, formula.type, formula.interval)
    f = GloballyUpIntersect(formula.clock, formula.type, formula.interval, formula.formula)
    lb = Label(singleton(), singleton(),
               singleton(f), singleton(t_pre), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[]_I p --> tb
def _expand_globally_up_3(formula: GloballyUp, label: Label, p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeGloballyPre(formula.clock, formula.type, formula.interval)
    lb = Label(singleton(), singleton(),
               singleton(), singleton(t_pre, TimeBound()), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[]_I p --> up[]down[]_I p
def _expand_globally_up_4(formula: GloballyUp, label: Label, p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeGloballyPre(formula.clock, formula.type, formula.interval)

    clk_index = label.max_clock_index + 1
    assert clock_index(formula.clock) < clk_index

    clk_s = [formula.clock, fresh_clock(clk_index)]
    ty_s = [formula.type, TypeVariable(clk_s[1].id)]

    r_clk, oc = ClkReset(clk_s[1]), OpenClose(ty_s[1])

    f = GloballyUpDown(clk_s[0], clk_s[1], ty_s[0], ty_s[1], formula.interval, formula.formula)
    lb = Label(singleton(), singleton(),
               singleton(f), singleton(t_pre, oc, r_clk), clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[]_I p --> up[*]down[]_I p
def _expand_globally_up_5(formula: GloballyUp, label: Label, p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeGloballyPre(formula.clock, formula.type, formula.interval)

    clk_index = label.max_clock_index + 1
    assert clock_index(formula.clock) < clk_index

    clk_s = [formula.clock, fresh_clock(clk_index)]
    ty_s = [formula.type, TypeVariable(clk_s[1].id)]

    r_clk, oc = ClkReset(clk_s[1]), OpenClose(ty_s[1])
    f = GloballyUpIntersectDown(clk_s[0], clk_s[1], ty_s[0], ty_s[1], formula.interval, formula.formula)
    lb = Label(singleton(), singleton(),
               singleton(f), singleton(t_pre, oc, r_clk), clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[*]_I p --> up[*]_I p
def _expand_globally_up_intersect_1(formula: GloballyUpIntersect, label: Label,
                                    p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpIntersect):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.formula), singleton(),
               singleton(formula), singleton(),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[*]_I p --> tb
def _expand_globally_up_intersect_2(formula: GloballyUpIntersect, label: Label,
                                    p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpIntersect):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.formula), singleton(),
               singleton(), singleton(TimeBound()), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[*]_I p --> up[*]down[]_I p
def _expand_globally_up_intersect_3(formula: GloballyUpIntersect, label: Label,
                                    p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpIntersect):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    clk_index = label.max_clock_index + 1

    assert clock_index(formula.clock) < clk_index
    clk_s = [formula.clock, fresh_clock(clk_index)]
    ty_s = [formula.type, TypeVariable(clk_s[1].id)]

    r_clk, oc = ClkReset(clk_s[1]), OpenClose(ty_s[1])

    f = GloballyUpIntersectDown(clk_s[0], clk_s[1], ty_s[0], ty_s[1], formula.interval, formula.formula)
    lb = Label(singleton(formula.formula), singleton(),
               singleton(f), singleton(oc, r_clk), clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[]down[]_I p --> up[]down[]_I p
def _expand_globally_up_down_1(formula: GloballyUpDown, label: Label,
                               p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeGloballyPre(formula.clock[0], formula.type[0], formula.interval)
    lb = Label(singleton(), singleton(),
               singleton(formula), singleton(t_pre), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[]down[]_I p --> up[*]down[]_I p
def _expand_globally_up_down_2(formula: GloballyUpDown, label: Label,
                               p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeGloballyPre(formula.clock[0], formula.type[0], formula.interval)
    f = GloballyUpIntersectDown(formula.clock[0], formula.clock[1], formula.type[0], formula.type[1],
                                formula.interval, formula.formula)
    lb = Label(singleton(), singleton(),
               singleton(f), singleton(t_pre), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[]down[]_I p --> tb
def _expand_globally_up_down_3(formula: GloballyUpDown, label: Label,
                               p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeGloballyPre(formula.clock[0], formula.type[0], formula.interval)
    lb = Label(singleton(), singleton(),
               singleton(), singleton(t_pre, TimeBound()), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[*]down[]_I p --> up[*]down[]_I p
def _expand_globally_up_intersect_down_1(formula: GloballyUpIntersectDown, label: Label,
                                         p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpIntersectDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.formula), singleton(),
               singleton(formula), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[*]down[]_I p --> final
def _expand_globally_up_intersect_down_2(formula: GloballyUpIntersectDown, label: Label,
                                         p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpIntersectDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_final = TimeGloballyFinal(formula.clock[1], formula.type[1], formula.interval)
    lb = Label(singleton(formula.formula), singleton(),
               singleton(), singleton(t_final), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up[*]down[]_I p --> tb
def _expand_globally_up_intersect_down_3(formula: GloballyUpIntersectDown, label: Label,
                                         p_label: Label) -> Optional[Label]:
    if not isinstance(formula, GloballyUpIntersectDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.formula), singleton(),
               singleton(), singleton(TimeBound()), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# <> p --> end
def _expand_untimed_finally_1(formula: FinallyFormula, label: Label,
                              p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyFormula):
        return None

    if not is_untimed(formula.local_time):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.child), singleton(),
               singleton(), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# <> p --> <> p
def _expand_untimed_finally_2(formula: FinallyFormula, label: Label,
                              p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyFormula):
        return None

    if not is_untimed(formula.local_time):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(), singleton(),
               singleton(formula), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# <>_I p --> up<>_I p
def _expand_timed_finally_1(formula: FinallyFormula, label: Label,
                            p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyFormula):
        return None

    if is_untimed(formula.local_time):
        return None

    pre_cond = [_non_redundant_goal(formula, p_label)]
    post_cond = []

    if not all(pre_cond):
        return None

    clk_index = label.max_clock_index + 1
    clk = fresh_clock(clk_index)
    r_clk = ClkReset(clk)

    ty = TypeVariable(clk.id)
    oc = OpenClose(ty)

    f = FinallyUp(clk, ty, formula.local_time, formula.child)

    lb = Label(singleton(f), singleton(oc, r_clk),
               singleton(), singleton(), clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# <>_I p --> up<*>_I p
def _expand_timed_finally_2(formula: FinallyFormula, label: Label,
                            p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyFormula):
        return None

    if is_untimed(formula.local_time):
        return None

    pre_cond = [_non_redundant_goal(formula, p_label)]
    post_cond = []

    if not all(pre_cond):
        return None

    clk_index = label.max_clock_index + 1
    clk = fresh_clock(clk_index)
    r_clk = ClkReset(clk)

    ty = TypeVariable(clk.id)
    oc = OpenClose(ty)

    f = FinallyUpIntersect(clk, ty, formula.local_time, formula.child)

    lb = Label(singleton(f), singleton(oc, r_clk),
               singleton(), singleton(), clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<>_I p --> up<>_I p
def _expand_finally_up_1(formula: FinallyUp, label: Label,
                         p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeFinallyPre(formula.clock, formula.type, formula.interval)

    lb = Label(singleton(), singleton(),
               singleton(formula), singleton(t_pre),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<>_I p --> up<*>_I p
def _expand_finally_up_2(formula: FinallyUp, label: Label,
                         p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeFinallyPre(formula.clock, formula.type, formula.interval)
    f = FinallyUpIntersect(formula.clock, formula.type, formula.interval, formula.formula)

    lb = Label(singleton(), singleton(),
               singleton(f), singleton(t_pre),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<>_I p --> up<>down<>_I p
def _expand_finally_up_3(formula: FinallyUp, label: Label,
                         p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    clk_index = label.max_clock_index + 1

    assert clock_index(formula.clock) < clk_index
    clk_s = [formula.clock, fresh_clock(clk_index)]
    ty_s = [formula.type, TypeVariable(clk_s[1].id)]

    r_clk = ClkReset(clk_s[1])
    oc = OpenClose(ty_s[1])

    t_pre = TimeFinallyPre(formula.clock, formula.type, formula.interval)
    f = FinallyUpDown(clk_s[0], clk_s[1], ty_s[0], ty_s[1], formula.interval, formula.formula)

    lb = Label(singleton(), singleton(),
               singleton(f), singleton(t_pre, oc, r_clk),
               clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<>_I p --> up<*>down<>_I p
def _expand_finally_up_4(formula: FinallyUp, label: Label,
                         p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUp):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    clk_index = label.max_clock_index + 1

    assert clock_index(formula.clock) < clk_index
    clk_s = [formula.clock, fresh_clock(clk_index)]
    ty_s = [formula.type, TypeVariable(clk_s[1].id)]

    r_clk = ClkReset(clk_s[1])
    oc = OpenClose(ty_s[1])

    t_pre = TimeFinallyPre(formula.clock, formula.type, formula.interval)
    f = FinallyUpIntersectDown(clk_s[0], clk_s[1], ty_s[0], ty_s[1], formula.interval, formula.formula)

    lb = Label(singleton(), singleton(),
               singleton(f), singleton(t_pre, oc, r_clk),
               clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>_I p --> up<*>_I p
def _expand_finally_up_intersect_1(formula: FinallyUpIntersect, label: Label,
                                   p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersect):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.formula), singleton(),
               singleton(formula), singleton(),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>_I p --> tb
def _expand_finally_up_intersect_2(formula: FinallyUpIntersect, label: Label,
                                   p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersect):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.formula), singleton(),
               singleton(), singleton(TimeBound()),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>_I p --> up<>_I p
def _expand_finally_up_intersect_3(formula: FinallyUpIntersect, label: Label,
                                   p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersect):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    r_clk = ClkAssn(formula.clock, inf(formula.interval))
    f = FinallyUp(formula.clock, formula.type, formula.interval, formula.formula)
    rst = TimeFinallyRestart(formula.clock, formula.type, formula.interval)

    if formula.interval.left_end:
        oc = Close(formula.type)
    else:
        oc = Open(formula.type)

    lb = Label(singleton(formula.formula), singleton(),
               singleton(f), singleton(r_clk, rst, oc),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>_I p --> up<>down<>_I p
def _expand_finally_up_intersect_4(formula: FinallyUpIntersect, label: Label,
                                   p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersect):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    # introduce a new clock
    clk_index = label.max_clock_index + 1

    assert clock_index(formula.clock) < clk_index
    clk_s = [formula.clock, fresh_clock(clk_index)]
    ty_s = [formula.type, TypeVariable(clk_s[1].id)]

    r_clk = ClkAssn(clk_s[0], inf(formula.interval))
    rst = TimeFinallyRestart(clk_s[0], ty_s[0], formula.interval)

    if formula.interval.left_end:
        oc = Close(formula.type)
    else:
        oc = Open(formula.type)

    oc2 = OpenClose(ty_s[1])
    r_clk2 = ClkReset(clk_s[1])

    f = FinallyUpDown(clk_s[0], clk_s[1], ty_s[0], ty_s[1], formula.interval, formula.formula)

    lb = Label(singleton(formula.formula), singleton(),
               singleton(f), singleton(r_clk, r_clk2, rst, oc, oc2),
               clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>_I p --> up<*>_I p
def _expand_finally_up_intersect_5(formula: FinallyUpIntersect, label: Label,
                                   p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersect):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    # introduce a new clock
    clk_index = label.max_clock_index + 1

    assert clock_index(formula.clock) < clk_index
    clk_s = [formula.clock, fresh_clock(clk_index)]
    ty_s = [formula.type, TypeVariable(clk_s[1].id)]

    oc = OpenClose(ty_s[1])
    r_clk = ClkReset(clk_s[1])

    f = FinallyUpIntersectDown(clk_s[0], clk_s[1], ty_s[0], ty_s[1], formula.interval, formula.formula)

    lb = Label(singleton(formula.formula), singleton(),
               singleton(f), singleton(r_clk, oc),
               clk_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<>down<>_I p --> up<>down<>_I p
def _expand_finally_up_down_1(formula: FinallyUpDown, label: Label,
                              p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeFinallyPre(formula.clock[0], formula.type[0], formula.interval)
    lb = Label(singleton(), singleton(),
               singleton(formula), singleton(t_pre),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<>down<>_I p --> up<*>down<>_I p
def _expand_finally_up_down_2(formula: FinallyUpDown, label: Label,
                              p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    t_pre = TimeFinallyPre(formula.clock[0], formula.type[0], formula.interval)
    f = FinallyUpIntersectDown(formula.clock[0], formula.clock[1],
                               formula.type[0], formula.type[1],
                               formula.interval, formula.formula)

    lb = Label(singleton(), singleton(),
               singleton(f), singleton(t_pre),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>down<>_I p --> up<*>down<>_I p
def _expand_finally_up_intersect_down_1(formula: FinallyUpIntersectDown, label: Label,
                                        p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersectDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.formula), singleton(),
               singleton(formula), singleton(),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>down<>_I p --> up<>down<>_I p
def _expand_finally_up_intersect_down_2(formula: FinallyUpIntersectDown, label: Label,
                                        p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersectDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    clk1, clk2 = formula.clock[0], formula.clock[1]
    ty1, ty2, interval = formula.type[0], formula.type[1], formula.interval
    f = FinallyUpDown(clk1, clk2, ty1, ty2, interval, formula.formula)

    r_clk1 = ClkAssn(clk1, inf(interval))
    r_clk2 = ClkReset(clk2)

    rst = TimeFinallyRestart(clk1, ty1, interval)

    if interval.left_end:
        oc = Close(ty1)
    else:
        oc = Open(ty1)

    lb = Label(singleton(formula.formula), singleton(),
               singleton(f), singleton(r_clk1, r_clk2, oc, rst),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>down<>_I p --> tb
def _expand_finally_up_intersect_down_3(formula: FinallyUpIntersectDown, label: Label,
                                        p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersectDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    lb = Label(singleton(formula.formula), singleton(),
               singleton(), singleton(TimeBound()),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# up<*>down<>_I p --> final
def _expand_finally_up_intersect_down_4(formula: FinallyUpIntersectDown, label: Label,
                                        p_label: Label) -> Optional[Label]:
    if not isinstance(formula, FinallyUpIntersectDown):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    final = TimeFinallyFinal(formula.clock[1], formula.type[1], formula.interval)

    lb = Label(singleton(formula.formula), singleton(),
               singleton(), singleton(final),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


def _expand_until_formula_1(formula: UntilFormula, label: Label,
                            p_label: Label) -> Optional[Label]:
    if not isinstance(formula, UntilFormula):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    assert is_untimed(formula.local_time)

    lb = Label(singleton(formula.left), singleton(),
               singleton(formula), singleton(),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


def _expand_until_formula_2(formula: UntilFormula, label: Label,
                            p_label: Label) -> Optional[Label]:
    if not isinstance(formula, UntilFormula):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    assert is_untimed(formula.local_time)

    lb = Label(singleton(formula.left, formula.right), singleton(),
               singleton(), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


def _expand_release_formula_1(formula: ReleaseFormula, label: Label,
                              p_label: Label) -> Optional[Label]:
    if not isinstance(formula, ReleaseFormula):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    assert is_untimed(formula.local_time)

    lb = Label(singleton(formula.left), singleton(),
               singleton(), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


def _expand_release_formula_2(formula: ReleaseFormula, label: Label,
                              p_label: Label) -> Optional[Label]:
    if not isinstance(formula, ReleaseFormula):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    assert is_untimed(formula.local_time)

    lb = Label(singleton(formula.right), singleton(),
               singleton(), singleton(TimeBound()),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


def _expand_release_formula_3(formula: ReleaseFormula, label: Label,
                              p_label: Label) -> Optional[Label]:
    if not isinstance(formula, ReleaseFormula):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    assert is_untimed(formula.local_time)

    lb = Label(singleton(formula.right), singleton(),
               singleton(formula), singleton(),
               label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


def _expand_and(formula: And, label: Label,
                p_label: Label) -> Optional[Label]:
    if not isinstance(formula, And):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    assert len(formula.children) == 2
    lf, rf = formula.children[0], formula.children[1]
    lb = Label(singleton(lf, rf), singleton(),
               singleton(), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


def _expand_or_1(formula: Or, label: Label,
                 p_label: Label) -> Optional[Label]:
    if not isinstance(formula, Or):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    assert len(formula.children) == 2
    lb = Label(singleton(formula.children[0]), singleton(),
               singleton(), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


def _expand_or_2(formula: Or, label: Label,
                 p_label: Label) -> Optional[Label]:
    if not isinstance(formula, Or):
        return None

    pre_cond = []
    post_cond = []

    if not all(pre_cond):
        return None

    assert len(formula.children) == 2
    lb = Label(singleton(formula.children[1]), singleton(),
               singleton(), singleton(), label.max_clock_index)

    for post in post_cond:
        if not post(lb):
            return None

    return lb


# update here
def update_waiting_list(formula: Formula, labels: Set[Tuple[FrozenSet[Formula], Label]],
                        elem: Tuple[Set[Formula], Label]) -> List[Tuple[Set[Formula], Label]]:
    w_f, lb = elem

    # update label
    lbs = update_labels(formula, labels, lb)
    return [(w_f.union(nc), u_lb) for nc, u_lb in lbs]


def update_labels(formula: Formula, labels: Set[Tuple[FrozenSet[Formula], Label]],
                  label: Label) -> List[Tuple[Set[Formula], Label]]:
    return [(set(c), Label(label.state_cur.union({formula}),
                           label.transition_cur.union(lb.transition_cur),
                           label.state_nxt.union(lb.state_nxt),
                           label.transition_nxt.union(lb.transition_nxt),
                           max(lb.max_clock_index, label.max_clock_index))) for c, lb in labels]


def _valid_time_bound(label: Label) -> bool:
    c, n = label.cur, label.nxt
    is_tb = TimeBound() in c

    # time bound cannot have next states
    if is_tb and len(n) > 0:
        return False

    # time bound cannot have state goals
    if is_tb and len(label.state_cur) > 0:
        return False

    return True


@singledispatch
def _non_redundant_goal(formula: Formula, p_label: Label) -> bool:
    return True


@_non_redundant_goal.register(GloballyFormula)
def _(formula: GloballyFormula, p_label: Label) -> bool:
    return formula not in p_label.cur


@_non_redundant_goal.register(FinallyFormula)
def _(formula: FinallyFormula, p_label: Label) -> bool:
    return formula not in p_label.cur


def _valid_clock(label: Label) -> bool:
    g_d, f_d = dict(), dict()
    for g in label.cur:
        _globally_clock_set(g, g_d)
        _finally_clock_set(g, f_d)

    for k in g_d:
        interval, formula = k
        clk_limit = _clock_upper_limit(interval)

        # if the clock set exceed the limit
        if len(g_d[k]) > clk_limit:
            return False

    for k in f_d:
        interval, formula = k
        clk_limit = _clock_upper_limit(interval)

        if len(f_d[k]) > clk_limit:
            return False

    # otherwise the label is valid
    return True

def _clock_upper_limit(interval: Interval) -> int:
    import math
    inf_v, sup_v = float(inf(interval).value), float(sup(interval).value)
    return math.ceil(sup_v / (sup_v - inf_v))


@singledispatch
def _globally_clock_set(formula: Formula, g_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    return


@_globally_clock_set.register(GloballyUp)
def _(formula: GloballyUp, g_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    k = (formula.interval, formula.formula)
    if k in g_dict:
        g_dict[k].add(formula.clock)
    else:
        g_dict[k] = {formula.clock}


@_globally_clock_set.register(GloballyUpIntersect)
def _(formula: GloballyUpIntersect, g_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    k = (formula.interval, formula.formula)
    if k in g_dict:
        g_dict[k].add(formula.clock)
    else:
        g_dict[k] = {formula.clock}


@_globally_clock_set.register(GloballyUpDown)
def _(formula: GloballyUpDown, g_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    k = (formula.interval, formula.formula)
    if k in g_dict:
        g_dict[k].add(formula.clock[0])
    else:
        g_dict[k] = {formula.clock[0]}


@_globally_clock_set.register(GloballyUpIntersectDown)
def _(formula: GloballyUpIntersectDown, g_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    k = (formula.interval, formula.formula)
    if k in g_dict:
        g_dict[k].add(formula.clock[0])
    else:
        g_dict[k] = {formula.clock[0]}


@singledispatch
def _finally_clock_set(formula: Formula, f_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    return


@_finally_clock_set.register(FinallyUp)
def _(formula: FinallyUp, f_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    k = (formula.interval, formula.formula)
    if k in f_dict:
        f_dict[k].add(formula.clock)
    else:
        f_dict[k] = {formula.clock}


@_finally_clock_set.register(FinallyUpIntersect)
def _(formula: FinallyUpIntersect, f_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    k = (formula.interval, formula.formula)
    if k in f_dict:
        f_dict[k].add(formula.clock)
    else:
        f_dict[k] = {formula.clock}


@_finally_clock_set.register(FinallyUpDown)
def _(formula: FinallyUpDown, f_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    k = (formula.interval, formula.formula)
    if k in f_dict:
        f_dict[k].add(formula.clock[0])
    else:
        f_dict[k] = {formula.clock[0]}


@_finally_clock_set.register(FinallyUpIntersectDown)
def _(formula: FinallyUpIntersectDown, f_dict: Dict[Tuple[Interval, Formula], Set[Real]]):
    k = (formula.interval, formula.formula)
    if k in f_dict:
        f_dict[k].add(formula.clock[0])
    else:
        f_dict[k] = {formula.clock[0]}


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


@_infer_temporal_formula.register(GloballyFormula)
def _(formula: GloballyFormula):
    return formula


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


@_infer_temporal_formula.register(FinallyFormula)
def _(formula: FinallyFormula):
    return formula


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
