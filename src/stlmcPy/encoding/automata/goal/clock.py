from typing import Optional

from .label import *
from ....constraints.aux.operations import *


class ClockSubstitution:
    def __init__(self):
        self._clock_subst_dict: Dict[Real, Real] = dict()

    def add(self, src: Real, dst: Real):
        self._clock_subst_dict[src] = dst

    def substitute(self, formula: Formula):
        return _clock_substitution(formula, self._clock_subst_dict)

    def __repr__(self):
        strings = ["ClockSubstitution"]
        for src in self._clock_subst_dict:
            strings.append("{} --> {}".format(src, self._clock_subst_dict[src]))
        return "\n".join(strings)


@singledispatch
def _clock_substitution(goal: Formula, clock_subst_dict: Dict[Real, Real]):
    return goal


@_clock_substitution.register(TypeHint)
def _(goal: TypeHint, clock_subst_dict: Dict[Real, Real]):
    if goal.get_clock() in clock_subst_dict:
        clk = clock_subst_dict[goal.get_clock()]
        return TypeHint(TypeVariable(clk.id), goal.value)
    else:
        # nothing to substitute
        return goal


@_clock_substitution.register(Up)
def _(goal: Up, clock_subst_dict: Dict[Real, Real]):
    is_clk = goal.clock in clock_subst_dict
    is_ty = isinstance(goal.type, TypeVariable)

    clk = clock_subst_dict[goal.clock] if is_clk else goal.clock
    ty = TypeVariable(clk.id) if is_ty else goal.type

    if isinstance(goal, GloballyUp):
        return GloballyUp(clk, ty, goal.interval, goal.formula)
    elif isinstance(goal, GloballyUpIntersect):
        return GloballyUpIntersect(clk, ty, goal.interval, goal.formula)
    elif isinstance(goal, FinallyUp):
        return FinallyUp(clk, ty, goal.interval, goal.formula)
    elif isinstance(goal, FinallyUpIntersect):
        return FinallyUpIntersect(clk, ty, goal.interval, goal.formula)
    else:
        raise Exception("wrong goal type")


@_clock_substitution.register(UpDown)
def _(goal: UpDown, clock_subst_dict: Dict[Real, Real]):
    is_clk = [goal.clock[0] in clock_subst_dict, goal.clock[1] in clock_subst_dict]
    is_ty = [isinstance(goal.type[0], TypeVariable), isinstance(goal.type[1], TypeVariable)]

    clk = [clock_subst_dict[goal.clock[0]] if is_clk[0] else goal.clock[0],
           clock_subst_dict[goal.clock[1]] if is_clk[1] else goal.clock[1]]
    ty = [TypeVariable(clk[0].id) if is_ty[0] else goal.type[0],
          TypeVariable(clk[1].id) if is_ty[1] else goal.type[1]]

    if isinstance(goal, GloballyUpDown):
        return GloballyUpDown(clk[0], clk[1], ty[0], ty[1], goal.interval, goal.formula)
    elif isinstance(goal, GloballyUpIntersectDown):
        return GloballyUpIntersectDown(clk[0], clk[1], ty[0], ty[1], goal.interval, goal.formula)
    elif isinstance(goal, FinallyUpDown):
        return FinallyUpDown(clk[0], clk[1], ty[0], ty[1], goal.interval, goal.formula)
    elif isinstance(goal, FinallyUpIntersectDown):
        return FinallyUpIntersectDown(clk[0], clk[1], ty[0], ty[1], goal.interval, goal.formula)
    else:
        raise Exception("wrong goal type")


@_clock_substitution.register(TimeProposition)
def _(goal: TimeProposition, clock_subst_dict: Dict[Real, Real]):
    is_clk = goal.clock in clock_subst_dict
    is_ty = isinstance(goal.ty, TypeVariable)

    clk = clock_subst_dict[goal.clock] if is_clk else goal.clock
    ty = TypeVariable(clk.id) if is_ty else goal.ty

    if isinstance(goal, TimeGloballyPre):
        return TimeGloballyPre(clk, ty, goal.interval)
    elif isinstance(goal, TimeGloballyFinal):
        return TimeGloballyFinal(clk, ty, goal.interval)
    elif isinstance(goal, TimeFinallyPre):
        return TimeFinallyPre(clk, ty, goal.interval)
    elif isinstance(goal, TimeFinallyFinal):
        return TimeFinallyFinal(clk, ty, goal.interval)
    elif isinstance(goal, TimeFinallyRestart):
        return TimeFinallyRestart(clk, ty, goal.interval)
    else:
        raise Exception("wrong goal type")


@_clock_substitution.register(ClkAssn)
def _(goal: ClkAssn, clock_subst_dict: Dict[Real, Real]):
    is_clk = goal.clock in clock_subst_dict

    clk = clock_subst_dict[goal.clock] if is_clk else goal.clock
    if isinstance(goal, ClkReset):
        return ClkReset(clk)
    elif isinstance(goal, ClkAssn):
        return ClkAssn(clk, goal.value)
    else:
        raise Exception("wrong goal type")


def global_clk_subst(max_depth: int) -> Dict[int, VarSubstitution]:
    clk_dict: Dict[int, VarSubstitution] = dict()

    cur_depth = 1
    while cur_depth <= max_depth:
        # clk_dict[cur_depth] = _global_clk_subst_at(cur_depth)
        cur_depth += 1

    return clk_dict


def global_clk():
    return Real("g@clk")


class ClockGenerator:
    def __init__(self):
        self._down_clock: Dict = dict()
        self._id_counter = 0

    def up_clock(self, formula: Formula):
        clk = [Real("clk{}".format(self._id_counter)),
               Real("clk{}".format(self._id_counter + 1))]

        assert (formula, clk[0]) not in self._down_clock
        self._down_clock[(formula, clk[0])] = clk[1]
        self._id_counter += 2

        return clk[0]

    def down_clock(self, formula: Formula, clock: Real):
        assert (formula, clock) in self._down_clock
        return self._down_clock[(formula, clock)]


def filter_clock_goals(*goals) -> Set[Formula]:
    clk_goals = set()
    for g in goals:
        clk_goals.update(_filter_clock_goals(g))
    return clk_goals


@singledispatch
def _filter_clock_goals(goal: Formula) -> Set[Formula]:
    return set()


@_filter_clock_goals.register(Up)
def _(goal: Up) -> Set[Formula]:
    return {goal}


@_filter_clock_goals.register(UpDown)
def _(goal: UpDown) -> Set[Formula]:
    return {goal}


@_filter_clock_goals.register(TimeProposition)
def _(goal: TimeProposition) -> Set[Formula]:
    return {goal}


@_filter_clock_goals.register(ClkReset)
def _(goal: ClkReset) -> Set[Formula]:
    return {goal}


def get_clock_pool(*goals) -> Set[Real]:
    clk_pool = set()
    for g in goals:
        clk_pool.update(_get_clocks(g))
    return clk_pool


@singledispatch
def _get_clocks(goal: Formula) -> Set[Real]:
    return set()


@_get_clocks.register(Up)
def _(goal: Up) -> Set[Real]:
    return {goal.clock}


@_get_clocks.register(UpDown)
def _(goal: UpDown) -> Set[Real]:
    return set(goal.clock)


@_get_clocks.register(TimeProposition)
def _(goal: TimeProposition) -> Set[Real]:
    return {goal.clock}


@_get_clocks.register(ClkReset)
def _(goal: ClkReset) -> Set[Real]:
    return {goal.clock}


def make_clk_type_mapping(*goals) -> Dict[Real, Set[str]]:
    mapping = dict()
    for goal in goals:
        _make_clk_type_mapping(goal, mapping)
    return mapping


@singledispatch
def _make_clk_type_mapping(goal: Formula, mapping: Dict[Real, Set[str]]):
    return


@_make_clk_type_mapping.register(Up)
def _(goal: Up, mapping: Dict[Real, Set[str]]):
    name = "{}_{}_{}_{}".format(goal.temporal, goal.type,
                                hash(goal.interval), hash(goal.formula))
    if goal.clock in mapping:
        mapping[goal.clock].add(name)
    else:
        mapping[goal.clock] = {name}


@_make_clk_type_mapping.register(UpDown)
def _(goal: UpDown, mapping: Dict[Real, Set[str]]):
    names = ["{}_{}_{}_{}_{}_F".format(goal.temporal1, goal.temporal2, goal.type[0],
                                       hash(goal.interval), hash(goal.formula)),
             "{}_{}_{}_{}_{}_B".format(goal.temporal1, goal.temporal2, goal.type[1],
                                       hash(goal.interval), hash(goal.formula))]

    for index, _ in enumerate(names):
        if goal.clock[index] in mapping:
            mapping[goal.clock[index]].add(names[index])
        else:
            mapping[goal.clock[index]] = {names[index]}


@_make_clk_type_mapping.register(TimeProposition)
def _(goal: TimeProposition, mapping: Dict[Real, Set[str]]):
    name = "T_{}_{}_{}".format(goal.temporal, goal.ty, hash(goal.interval))
    if goal.clock in mapping:
        mapping[goal.clock].add(name)
    else:
        mapping[goal.clock] = {name}


@_make_clk_type_mapping.register(ClkReset)
def _(goal: ClkReset, mapping: Dict[Real, Set[str]]):
    name = "clk_assn"
    if goal.clock in mapping:
        mapping[goal.clock].add(name)
    else:
        mapping[goal.clock] = {name}
