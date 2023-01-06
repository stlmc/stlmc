from typing import Optional, Tuple

from .label import *
from ....constraints.aux.operations import *


class ClockSubstitution:
    def __init__(self):
        self._clock_subst_dict: Dict[Real, Real] = dict()

    def add(self, src: Real, dst: Real):
        self._clock_subst_dict[src] = dst

    def is_in(self, clk: Real):
        return clk in self._clock_subst_dict

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


@_clock_substitution.register(OCProposition)
def _(goal: OCProposition, clock_subst_dict: Dict[Real, Real]):
    if goal.get_clock() in clock_subst_dict:
        clk = clock_subst_dict[goal.get_clock()]
        if isinstance(goal, Open):
            return Open(TypeVariable(clk.id))
        elif isinstance(goal, Close):
            return Close(TypeVariable(clk.id))
        elif isinstance(goal, OpenClose):
            return OpenClose(TypeVariable(clk.id))
        else:
            raise Exception("wrong goal type")
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


def fresh_clock(index: int) -> Real:
    return Real("clk{}".format(index))


def clock_index(clock: Real) -> int:
    return int(clock.id[3:])


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


@_filter_clock_goals.register(ClkAssn)
def _(goal: ClkAssn) -> Set[Formula]:
    return {goal}


@_filter_clock_goals.register(OCProposition)
def _(goal: OCProposition) -> Set[Formula]:
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


class ClockMatchingInfo:
    def __init__(self):
        self._matching_info: Dict[Tuple[str, hash, hash], List[Real]] = dict()

    def add(self, goal: Formula):
        info = _matching_info(goal)

        # do nothing
        if info is None:
            return

        assert info not in self._matching_info
        self._matching_info[info] = _get_matching_clocks(goal)

    def match(self, other: 'ClockMatchingInfo') -> Optional[ClockSubstitution]:
        assert isinstance(other, ClockMatchingInfo)

        # information must be equal
        if set(self._matching_info.keys()) != set(other._matching_info.keys()):
            return None

        clk_subst = ClockSubstitution()
        for k in other._matching_info:
            o_k = zip(self._matching_info[k], other._matching_info[k])
            # other's clock is renamed to self's clock
            for c1, c2 in o_k:
                # if already exists, clocks cannot be matched
                if clk_subst.is_in(c2):
                    return None

                clk_subst.add(c2, c1)

        return clk_subst


@singledispatch
def _matching_info(goal: Formula) -> Optional[Tuple[str, hash, hash]]:
    return None


@_matching_info.register(Up)
def _(goal: Up) -> Optional[Tuple[str, hash, hash]]:
    return goal.temporal, hash(goal.interval), hash(goal.formula)


@_matching_info.register(UpDown)
def _(goal: UpDown) -> Optional[Tuple[str, hash, hash]]:
    return "{}{}".format(goal.temporal1, goal.temporal2), hash(goal.interval), hash(goal.formula)


@_matching_info.register(TimeProposition)
def _(goal: TimeProposition) -> Optional[Tuple[str, hash, hash]]:
    return "T{}_{}".format(goal.temporal, goal.name_s), hash(goal.interval), 0


@_matching_info.register(ClkAssn)
def _(goal: ClkAssn) -> Optional[Tuple[str, hash, hash]]:
    return "assn", hash(goal.value), 0


@_matching_info.register(Open)
def _(goal: Open) -> Optional[Tuple[str, hash, hash]]:
    return "open", 0, 0


@_matching_info.register(Close)
def _(goal: Close) -> Optional[Tuple[str, hash, hash]]:
    return "close", 0, 0


@_matching_info.register(OpenClose)
def _(goal: OpenClose) -> Optional[Tuple[str, hash, hash]]:
    return "oc", 0, 0


@singledispatch
def _get_matching_clocks(goal: Formula) -> List[Real]:
    return list()


@_get_matching_clocks.register(Up)
def _(goal: Up) -> List[Real]:
    return [goal.clock]


@_get_matching_clocks.register(UpDown)
def _(goal: UpDown) -> List[Real]:
    return goal.clock.copy()


@_get_matching_clocks.register(TimeProposition)
def _(goal: TimeProposition) -> List[Real]:
    return [goal.clock]


@_get_matching_clocks.register(ClkAssn)
def _(goal: ClkAssn) -> List[Real]:
    return [goal.clock]


@_get_matching_clocks.register(OCProposition)
def _(goal: OCProposition) -> List[Real]:
    return [goal.get_clock()]
