from typing import Optional, Iterator, Set

from stlmcPy.constraints.constraints import Dynamics, Constraint


# mutable
class BaseMode:
    def __init__(self, name, ha):
        self.incoming = set()
        self.outgoing = set()
        self.name = name
        self._dynamics = None
        self._invariant = None
        self.chi_valuation = dict()
        self.ha = ha

    def __hash__(self):
        return hash(id(self))

    def __lt__(self, other):
        return self.__hash__() < other.__hash__()

    @property
    def dynamics(self):
        return self._dynamics

    def set_dynamics(self, dyn: Dynamics):
        self._dynamics = dyn

    @property
    def invariant(self):
        return self._invariant

    def set_invariant(self, inv: Constraint):
        self._invariant = inv

    def belongs_to(self):
        return self.ha


class AggregatedMode(BaseMode, Set):
    def add(self, item: BaseMode):
        return self._modes.add(item)

    def __iter__(self) -> Iterator[Set]:
        return iter(self._modes)

    def __len__(self) -> int:
        return self._modes.__len__()

    def __contains__(self, x: object) -> bool:
        return self._modes.__contains__(x)

    def __init__(self, name, set_of_modes: set, ha):
        super().__init__(name, ha)
        self._modes = set_of_modes
        self._dynamics = None
        self._invariant = None

    def __repr__(self):
        if self.ha is None:
            return "( aggregated mode None_{} = dyn: {} inv: {} )".format(self.name, self.dynamics, self.invariant)
        return "( aggregated mode {}_{} = dyn: {}, inv: {} )".format(self.ha.name, self.name, self._dynamics, self._invariant)


class Mode(BaseMode):
    def __init__(self, name, ha):
        super().__init__(name, ha)

    def __repr__(self):
        if self.ha is None:
            return "( mode None_{} = dyn: {} inv: {} )".format(self.name, self.dynamics, self.invariant)
        return "( mode {}_{} = dyn: {} inv: {} )".format(self.ha.name, self.name, self.dynamics, self.invariant)


# immutable
class Transition:
    def __init__(self, name: str, src: Mode, trg: Mode, ha):
        self.ha = ha
        self.name = name
        self.src = src
        self.trg = trg
        self.guard = None
        self.reset = None

    def set_guard(self, const: Constraint):
        self.guard = const

    def set_reset(self, const: Constraint):
        self.reset = const

    def belongs_to(self):
        return self.ha

    def __hash__(self):
        return hash(id(self))

    def __repr__(self):
        return "[{}, {}: {} -> {}, guard: {}, reset: {}]".format(self.ha.name, self.name, self.src.name,
                                                                 self.trg.name, self.guard, self.reset)


# mutable, for aggregation
class HybridAutomaton:
    def __init__(self, name):
        self.name = name
        self.modes = set()
        self.transitions = set()

    def new_mode(self, name: str, is_aggregated=False) -> Mode:
        if not is_aggregated:
            mode = Mode(name, self)
        else:
            mode = AggregatedMode(name, set(), self)
        self.modes.add(mode)
        return mode

    def new_transition(self, name: str, src: Mode, trg: Mode) -> Transition:
        trans = Transition(name, src, trg, self)
        self.transitions.add(trans)
        src.outgoing.add(trans)
        trg.incoming.add(trans)
        return trans

    def __repr__(self):
        ha_str = "hybrid automaton {}".format(self.name)
        for i, mode in enumerate(self.modes):
            if i == 0:
                ha_str += "\n  Modes:\n  {}\n".format(mode)
            elif i < len(self.modes) - 1:
                ha_str += "  {}\n".format(mode)
            else:
                ha_str += "  {}".format(mode)

        for i, trans in enumerate(self.transitions):
            if i == 0:
                ha_str += "\n  Transitions:\n  {}\n".format(trans)
            elif i < len(self.transitions) - 1:
                ha_str += "  {}\n".format(trans)
            else:
                ha_str += "  {}".format(trans)
        return ha_str
