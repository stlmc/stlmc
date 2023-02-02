from itertools import permutations
from typing import Tuple

from .label import *
from ....constraints.aux.operations import *


class ClockSubstitution:
    def __init__(self):
        self._clock_subst_dict: Dict[Real, Real] = dict()

    def add(self, src: Real, dst: Real):
        self._clock_subst_dict[src] = dst

    def substitute(self, formula: Formula, is_write=True, is_read=True):
        return _clock_substitution(formula, self._clock_subst_dict, is_write=is_write, is_read=is_read)

    def vars(self) -> Set[Real]:
        return set(self._clock_subst_dict.keys())

    def clock_assn(self) -> Set[ClkAssn]:
        clk_assn = set()
        for clk in self._clock_subst_dict:
            clk_assn.add(ClkAssn(clk, self._clock_subst_dict[clk]))
        return clk_assn

    def dict(self) -> Dict[Real, Real]:
        return self._clock_subst_dict.copy()

    def __repr__(self):
        strings = ["ClockSubstitution"]
        for src in self._clock_subst_dict:
            strings.append("{} --> {}".format(src, self._clock_subst_dict[src]))
        return "\n".join(strings)


@singledispatch
def _clock_substitution(goal: Formula, clock_subst_dict: Dict[Real, Real],
                        is_write: bool, is_read: bool):
    return goal


@_clock_substitution.register(OCProposition)
def _(goal: OCProposition, clock_subst_dict: Dict[Real, Real],
      is_write: bool, is_read: bool):
    if is_read:
        return goal
    else:
        # The variable of the OCProposition is writable
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
def _(goal: Up, clock_subst_dict: Dict[Real, Real], is_write: bool, is_read: bool):
    is_clk = goal.clock in clock_subst_dict

    clk = clock_subst_dict[goal.clock] if is_clk else goal.clock
    ty = TypeVariable(clk.id)

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
def _(goal: UpDown, clock_subst_dict: Dict[Real, Real], is_write: bool, is_read: bool):
    is_clk = [goal.clock[0] in clock_subst_dict, goal.clock[1] in clock_subst_dict]

    clk = [clock_subst_dict[goal.clock[0]] if is_clk[0] else goal.clock[0],
           clock_subst_dict[goal.clock[1]] if is_clk[1] else goal.clock[1]]
    ty = [TypeVariable(clk[0].id),
          TypeVariable(clk[1].id)]

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
def _(goal: TimeProposition, clock_subst_dict: Dict[Real, Real], is_write: bool, is_read: bool):
    if is_read:
        is_clk = goal.clock in clock_subst_dict

        clk = clock_subst_dict[goal.clock] if is_clk else goal.clock
        ty = TypeVariable(clk.id)

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
    else:
        return goal


@_clock_substitution.register(ClkAssn)
def _(goal: ClkAssn, clock_subst_dict: Dict[Real, Real],
      is_write: bool, is_read: bool):
    f = goal
    if is_write:
        f = _substitute_clk_assn_as_write(f, clock_subst_dict)

    if is_read:
        f = _substitute_clk_assn_as_read(f, clock_subst_dict)
    return f


def _substitute_clk_assn_as_write(goal: ClkAssn, clock_subst_dict: Dict[Real, Real]):
    is_clk = goal.clock in clock_subst_dict

    clk = clock_subst_dict[goal.clock] if is_clk else goal.clock
    if isinstance(goal, ClkAssn):
        return ClkAssn(clk, goal.value)
    else:
        raise Exception("wrong goal type")


def _substitute_clk_assn_as_read(goal: ClkAssn, clock_subst_dict: Dict[Real, Real]):
    is_rv = goal.value in clock_subst_dict

    v = clock_subst_dict[goal.value] if is_rv else goal.value
    if isinstance(goal, ClkAssn):
        return ClkAssn(goal.clock, v)
    else:
        raise Exception("wrong goal type")


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
        if _is_clock_goals(g):
            clk_goals.add(g)
    return clk_goals


@singledispatch
def _is_clock_goals(goal: Formula) -> bool:
    return False


@_is_clock_goals.register(Up)
def _(goal: Up) -> bool:
    return True


@_is_clock_goals.register(UpDown)
def _(goal: UpDown) -> bool:
    return True


@_is_clock_goals.register(TimeProposition)
def _(goal: TimeProposition) -> bool:
    return True


@_is_clock_goals.register(ClkAssn)
def _(goal: ClkAssn) -> bool:
    return True


@_is_clock_goals.register(OCProposition)
def _(goal: OCProposition) -> bool:
    return True


def get_clock_pool(*goals, at_read=True, at_write=True) -> Set[Real]:
    clk_pool = set()
    for g in goals:
        clk_pool.update(_get_clocks(g, at_read, at_write))
    return clk_pool


@singledispatch
def _get_clocks(goal: Formula, at_read: bool, at_write: bool) -> Set[Real]:
    return set()


@_get_clocks.register(Up)
def _(goal: Up, at_read: bool, at_write: bool) -> Set[Real]:
    return {goal.clock}


@_get_clocks.register(UpDown)
def _(goal: UpDown, at_read: bool, at_write: bool) -> Set[Real]:
    return set(goal.clock)


@_get_clocks.register(TimeProposition)
def _(goal: TimeProposition, at_read: bool, at_write: bool) -> Set[Real]:
    clk_s = set()
    if at_read:
        clk_s.add(goal.clock)

    return clk_s


@_get_clocks.register(ClkAssn)
def _(goal: ClkAssn, at_read: bool, at_write: bool) -> Set[Real]:
    clk_s = set()
    if at_read:
        clk_s.add(goal.clock)

    if at_write:
        if isinstance(goal.value, Real):
            clk_s.add(goal.value)

    return clk_s


@_get_clocks.register(OCProposition)
def _(goal: OCProposition, at_read: bool, at_write: bool) -> Set[Real]:
    clk_s = set()
    if at_write:
        clk_s.add(goal.get_clock())
    return clk_s
