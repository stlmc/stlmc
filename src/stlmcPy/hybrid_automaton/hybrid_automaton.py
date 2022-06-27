from typing import Optional, Iterator, Set

from ..constraints.constraints import Dynamics, Constraint, And

# mutable


class BaseMode:
    def __init__(self, name, ha):
        self.incoming = set()
        self.outgoing = set()

        self._dynamics = set()
        self._invariant = set()

        self.ha = ha
        self.name = name

    def __hash__(self):
        return hash(id(self))

    def __lt__(self, other):
        return self.__hash__() < other.__hash__()

    @property
    def dynamics(self):
        return self._dynamics

    def set_dynamic(self, var, exp):
        self._dynamics.add((var, exp))

    def remove_dynamic(self, var, exp):
        try:
            self._dynamics.remove((var, exp))
        except KeyError:
            pass

    def remove_dynamics(self, dynamics: Set):
        self._dynamics = self._dynamics.difference(dynamics)

    @property
    def invariant(self):
        return self._invariant

    def set_invariant(self, inv: Constraint):
        # flatten "And"
        if isinstance(inv, And):
            for child in inv.children:
                self._invariant.add(child)
        else:
            self._invariant.add(inv)

    def remove_invariant(self, inv: Constraint):
        try:
            self._invariant.remove(inv)
        except KeyError:
            pass

    def remove_invariants(self, invariants: Set):
        self._invariant = self._invariant.difference(invariants)

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
        self._dynamics = set()
        self._invariant = set()

    def __repr__(self):
        simple_ha_name = self.ha.name
        if len(self.ha.name) > 20:
            simple_ha_name = "{} ...".format(simple_ha_name[:20])
        exact_name = self.name
        if len(exact_name) > 20:
            exact_name = "{} ...".format(exact_name[:20])
        if self.ha is None:
            return "( aggregated mode None_{} = dyn: {} inv: {} )".format(exact_name, self.dynamics, self.invariant)
        return "( aggregated mode {}_{} = dyn: {}, inv: {} )".format(simple_ha_name, exact_name, self._dynamics, self._invariant)


class Mode(BaseMode):
    def __init__(self, name, ha):
        super().__init__(name, ha)

    def __repr__(self):
        simple_ha = self.ha.name
        if len(simple_ha) > 20:
            simple_ha = "{} ...".format(simple_ha)
        exact_name = self.name
        if len(exact_name) > 20:
            exact_name = "{} ...".format(exact_name[:20])
        if self.ha is None:
            return "( mode None_{} = dyn: {} inv: {} )".format(exact_name, self.dynamics, self.invariant)
        return "( mode {}_{} = dyn: {} inv: {} )".format(simple_ha, exact_name, self.dynamics, self.invariant)


# immutable
class Transition:
    def __init__(self, name: str, src: Mode, trg: Mode, ha):
        self.ha = ha
        self.name = name
        self.src = src
        self.trg = trg
        self.guard = set()
        self.reset = set()

    def set_guard(self, const: Constraint):
        # flatten "And"
        if isinstance(const, And):
            for child in const.children:
                self.guard.add(child)
        else:
            self.guard.add(const)

    def remove_guard(self, const: Constraint):
        try:
            self.guard.remove(const)
        except KeyError:
            pass

    def remove_guards(self, guards: Set):
        self.guard = self.reset.difference(guards)

    def set_reset(self, const: Constraint):
        # flatten "And"
        if isinstance(const, And):
            for child in const.children:
                self.reset.add(child)
        else:
            self.reset.add(const)

    def remove_reset(self, const: Constraint):
        try:
            self.reset.remove(const)
        except KeyError:
            pass

    def remove_resets(self, resets: Set):
        self.reset = self.reset.difference(resets)

    def belongs_to(self):
        return self.ha

    def __hash__(self):
        return hash(id(self))

    def __repr__(self):
        simple_ha = self.ha.name
        if len(simple_ha) > 20:
            simple_ha = "{} ...".format(simple_ha)
        exact_name = self.name
        if len(exact_name) > 20:
            exact_name = "{} ...".format(exact_name)
        return "[{}, {}: {} -> {}, guard: {}, reset: {}]".format(simple_ha, exact_name, self.src.name,
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
        ha_str = "hybrid automaton"
        exact_name = self.name
        if len(exact_name) > 20:
            exact_name = "{} ...".format(exact_name[:20])

        ha_str = "hybrid automaton {}".format(exact_name)
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
