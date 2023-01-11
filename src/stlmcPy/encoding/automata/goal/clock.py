from itertools import permutations
from typing import Optional, Tuple

from .label import *
from ....constraints.aux.operations import *


class ClockSubstitution:
    def __init__(self):
        self._clock_subst_dict: Dict[Real, Real] = dict()

    def add(self, src: Real, dst: Real):
        self._clock_subst_dict[src] = dst

    def substitute(self, formula: Formula):
        return _clock_substitution(formula, self._clock_subst_dict)

    def clock_assn(self) -> Set[ClkAssn]:
        clk_assn = set()
        for clk in self._clock_subst_dict:
            clk_assn.add(ClkAssn(clk, self._clock_subst_dict[clk]))
        return clk_assn

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
    elif isinstance(goal, TimeGloballyUpFinal):
        return TimeGloballyUpFinal(clk, ty, goal.interval)
    elif isinstance(goal, TimeGloballyIn):
        return TimeGloballyIn(clk, ty, goal.interval)
    elif isinstance(goal, TimeFinallyPre):
        return TimeFinallyPre(clk, ty, goal.interval)
    elif isinstance(goal, TimeFinallyUpFinal):
        return TimeFinallyUpFinal(clk, ty, goal.interval)
    elif isinstance(goal, TimeFinallyIn):
        return TimeFinallyIn(clk, ty, goal.interval)
    else:
        raise Exception("wrong goal type")


@_clock_substitution.register(ClkAssn)
def _(goal: ClkAssn, clock_subst_dict: Dict[Real, Real]):
    is_clk = goal.clock in clock_subst_dict
    is_rv = goal.value in clock_subst_dict

    clk = clock_subst_dict[goal.clock] if is_clk else goal.clock
    v = clock_subst_dict[goal.value] if is_rv else goal.value
    if isinstance(goal, ClkReset):
        return ClkReset(clk)
    elif isinstance(goal, ClkAssn):
        return ClkAssn(clk, v)
    else:
        raise Exception("wrong goal type")


def global_clk_subst(max_depth: int) -> Dict[int, VarSubstitution]:
    clk_dict: Dict[int, VarSubstitution] = dict()

    cur_depth = 1
    while cur_depth <= max_depth:
        # clk_dict[cur_depth] = _global_clk_subst_at(cur_depth)
        cur_depth += 1

    return clk_dict


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
        self._matching_info_cur: Dict[Tuple[str, hash, hash], List[List[Real]]] = dict()
        self._matching_info_nxt: Dict[Tuple[str, hash, hash], List[List[Real]]] = dict()

    def add_cur(self, goal: Formula):
        self._add(goal, self._matching_info_cur)

    def add_nxt(self, goal: Formula):
        self._add(goal, self._matching_info_nxt)

    @classmethod
    def _add(cls, goal: Formula, d: Dict[Tuple[str, hash, hash], List[List[Real]]]):
        info = _matching_info(goal)

        if info is None:
            return

        if info in d:
            d[info].append(_get_matching_clocks(goal))
        else:
            d[info] = [_get_matching_clocks(goal)]

    def match(self, other: 'ClockMatchingInfo') -> Optional[ClockSubstitution]:
        assert isinstance(other, ClockMatchingInfo)

        k_c = set(self._matching_info_cur.keys())
        # information must be equal
        if k_c != set(other._matching_info_cur.keys()):
            return None

        subst = _match(list(k_c), other._matching_info_cur, self._matching_info_cur, dict())
        if subst is None:
            return None

        k_n = set(self._matching_info_nxt.keys())
        if k_n != set(other._matching_info_nxt.keys()):
            return None

        subst = _match(list(k_n), other._matching_info_nxt, self._matching_info_nxt, subst)
        if subst is None:
            return None

        clk_subst = ClockSubstitution()
        for k in subst:
            clk_subst.add(k, subst[k])

        return clk_subst

    def __repr__(self):
        cur = "\n".join(["{} ---> {}".format(k, self._matching_info_cur[k]) for k in self._matching_info_cur])
        nxt = "\n".join(["{} ---> {}".format(k, self._matching_info_nxt[k]) for k in self._matching_info_nxt])
        return "clock matching\ncur:\n{}\nnxt:\n{}\n".format(cur, nxt)


def _match(positions: List[Tuple[str, hash, hash]],
           match1: Dict[Tuple[str, hash, hash], List[List[Real]]],
           match2: Dict[Tuple[str, hash, hash], List[List[Real]]],
           subst: Dict[Real, Real]) -> Optional[Dict[Real, Real]]:
    if len(positions) <= 0:
        return subst

    pos = positions.pop(0)
    p_clk1, p_clk2 = match1[pos], match2[pos]

    if len(p_clk1) != len(p_clk2):
        return None

    p_clk2_order = list(map(lambda x: list(x), permutations(p_clk2)))

    for clk2_set in p_clk2_order:
        n_subst = _match_test(subst, p_clk1, clk2_set)
        if n_subst is None:
            continue

        m = _match(positions, match1, match2, n_subst)
        if m is not None:
            return m
    return None


def _match_test(subst: Dict[Real, Real],
                c1_set: List[List[Real]], c2_set: List[List[Real]]) -> Optional[Dict[Real, Real]]:
    new_subst = subst.copy()
    for clk1_s, clk2_s in list(zip(c1_set, c2_set)):
        new_subst = _match_clk(new_subst, clk1_s, clk2_s)
        if new_subst is None:
            return None
    return new_subst


def _match_clk(subst: Dict[Real, Real],
               c1_set: List[Real], c2_set: List[Real]) -> Optional[Dict[Real, Real]]:
    new_subst = subst.copy()
    for c1, c2 in set(zip(c1_set, c2_set)):
        # conflict
        if c1 in subst:
            if not variable_equal(subst[c1], c2):
                return None
        new_subst[c1] = c2
    return new_subst


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
    return "T_{{{},{}}}".format(goal.temporal, goal.name_s), hash(goal.interval), 0


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
