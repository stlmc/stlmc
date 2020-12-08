import abc
from collections import Set
from typing import Optional, Iterator, Tuple, Set

import z3

from stlmcPy.constraints.constraints import Dynamics, Constraint
# mutable
from stlmcPy.constraints.operations import get_vars
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.z3 import z3Obj


class BaseMode:
    def __init__(self):
        self.incoming = set()
        self.outgoing = set()
        self.name = ""
        self._dynamics = None
        self._invariant = None

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


class AggregatedMode(BaseMode, Set):
    def add(self, item: BaseMode):
        return self._modes.add(item)

    def __iter__(self) -> Iterator[Set]:
        return iter(self._modes)

    def __len__(self) -> int:
        return self._modes.__len__()

    def __contains__(self, x: object) -> bool:
        return self._modes.__contains__(x)

    def __init__(self, name, set_of_modes: set):
        super().__init__()
        self.name = name
        self._modes = set_of_modes
        self._dynamics = None
        self._invariant = None

    def __repr__(self):
        return "aggregated mode {}, dyn: {}, inv: {}".format(self.name, self._dynamics, self._invariant)


class Mode(BaseMode):
    def __init__(self, name):
        super().__init__()
        self.name = name

    def __hash__(self):
        return hash(str(self.name))

    def __repr__(self):
        return "{}, dyn: {}, inv: {}".format(self.name, self.dynamics, self.invariant)


# immutable
class Transition:
    def __init__(self, name: str, src: Mode, trg: Mode):
        self._name = name
        self.src = src
        self.trg = trg
        self.guard = None
        self.reset = None

    def set_guard(self, const: Constraint):
        self.guard = const

    def set_reset(self, const: Constraint):
        self.reset = const

    @property
    def name(self):
        return self._name

    def __hash__(self):
        return hash(self.__repr__())

    def __repr__(self):
        return "[{}: {} -> {}, guard: {}, reset: {}]".format(self.name, self.src.name,
                                                             self.trg.name, self.guard, self.reset)


# mutable, for aggregation
class HybridAutomaton:
    def __init__(self, uid):
        self._id = uid
        self._modes = dict()
        self._trans = dict()
        # this is same as the self._trans
        # but its key is a depth
        # Map[Mode, List[Transition]]
        self._trans_with_depth = dict()
        self.init_const = None
        self._err_mode = None

    @property
    def name(self):
        return self._id

    @property
    def trans(self):
        return self._trans

    @property
    def trans_with_depth(self):
        return self._trans_with_depth

    @property
    def modes(self):
        return self._modes

    @property
    def error_mode(self) -> Optional[Mode]:
        return self._err_mode

    def set_init(self, const: Constraint):
        self.init_const = const

    def new_mode(self, name: str, is_aggregated=False, is_error=False) -> Mode:
        # mode name should be unique.
        if name not in self.modes:
            if not is_aggregated:
                self.modes[name] = Mode(name)
                if is_error:
                    self._err_mode = self.modes[name]
                return self.modes[name]
            else:
                self.modes[name] = AggregatedMode(name, set())
                return self.modes[name]
        return self.modes[name]

    def new_transition(self, name: str, src: Mode, trg: Mode) -> Transition:
        # if in the hybrid_automaton
        if name not in self.trans:
            new_trans = Transition(name, src, trg)
            self.trans[name] = new_trans
            src.outgoing.add(new_trans)
            trg.incoming.add(new_trans)
            return new_trans
        return self.trans[name]

    def __repr__(self):
        trans_str = "hybrid automaton {}".format(self._id)
        for i, k in enumerate(self.modes):
            if i == 0:
                trans_str += "\n  Modes:\n  {}\n".format(repr(self.modes[k]))
            elif i < len(self.modes) - 1:
                trans_str += "  {}\n".format(repr(self.modes[k]))
            else:
                trans_str += "  {}".format(repr(self.modes[k]))

        for i, k in enumerate(self.trans):
            if i == 0:
                trans_str += "\n  Transitions:\n  {}\n".format(repr(self.trans[k]))
            elif i < len(self.trans) - 1:
                trans_str += "  {}\n".format(repr(self.trans[k]))
            else:
                trans_str += "  {}".format(repr(self.trans[k]))
        return trans_str


# c1 subsumes c2
def subsumption(c1: Constraint, c2: Constraint):
    if c1 is None:
        if c2 is None:
            return True
        return False
    if c2 is None:
        return True

    var_set = get_vars(c1)
    var_set = var_set.union(get_vars(c2))

    var_list = list()
    for v in var_set:
        var_list.append(z3Obj(v))

    left = z3Obj(c1)
    right = z3Obj(c2)

    f = z3.ForAll(var_list, z3.Implies(left, right))
    s = z3.Solver()
    s.add(f)
    # print(s.sexpr())
    str_result = str(s.check())
    # print(str_result)
    if str_result == "sat":
        return True
    else:
        return False


def merge_mode(m1: BaseMode, m2: BaseMode) -> Tuple[Optional[AggregatedMode], bool]:
    if m1.dynamics == m2.dynamics:
        ha2_subsume_ha1 = subsumption(m2.invariant, m1.invariant)
        ha1_subsume_ha2 = subsumption(m1.invariant, m2.invariant)
        if not ha2_subsume_ha1 and not ha1_subsume_ha2:
            # print("cannot merge {} and {}".format(m1.name, m2.name))
            return None, False

        new_agg_mode = AggregatedMode("{}+{}".format(m1.name, m2.name), set())
        new_agg_mode.add(m1)
        new_agg_mode.add(m2)
        new_agg_mode.set_dynamics(m1.dynamics)
        if ha2_subsume_ha1:
            new_agg_mode.set_invariant(m1.invariant)
        else:
            # ha1_subsume_ha2
            new_agg_mode.set_invariant(m2.invariant)
        new_agg_mode.incoming = new_agg_mode.incoming.union(m1.incoming)
        new_agg_mode.incoming = new_agg_mode.incoming.union(m2.incoming)

        new_agg_mode.outgoing = new_agg_mode.incoming.union(m1.outgoing)
        new_agg_mode.outgoing = new_agg_mode.incoming.union(m2.outgoing)
        return new_agg_mode, True
    else:
        return None, False


def merge_modes(ha: HybridAutomaton, modes: Set[BaseMode]) -> Tuple[Optional[AggregatedMode], bool]:
    agg_set = set()
    dynamics = None
    for m in modes:
        if m.dynamics == mode.dynamics:
            ha2_subsume_ha1 = subsumption(mode.invariant, m.invariant)
            ha1_subsume_ha2 = subsumption(m.invariant, mode.invariant)
            if not ha2_subsume_ha1 and not ha1_subsume_ha2:
                # print("cannot merge {} and {}".format(m1.name, m2.name))
                continue
            dynamics = m.dynamics
            agg_set.add(m)
            agg_set.add(mode)
            # new_agg_mode = AggregatedMode("{}+{}".format(m.name, mode.name), set())
            # new_agg_mode.add(m)
            # new_agg_mode.add(m2)
            # new_agg_mode.set_dynamics(m1.dynamics)
            if ha2_subsume_ha1:
                new_agg_mode.set_invariant(m1.invariant)
            else:
                # ha1_subsume_ha2
                new_agg_mode.set_invariant(m2.invariant)
            return new_agg_mode, True
        else:
            return None, False


# assumption2: ha1 and ha2 has the same depth
# assumption3: no cycle exists
def merge(ha1: HybridAutomaton, ha2: HybridAutomaton) -> HybridAutomaton:
    ha = HybridAutomaton("{}+{}".format(ha1.name, ha2.name))
    err1_mode = ha1.error_mode
    err2_mode = ha2.error_mode

    if err1_mode is not None and err2_mode is not None:

        waiting_list = set()
        waiting_list.update(err1_mode.incoming)
        waiting_list.update(err2_mode.incoming)
        print(waiting_list)

        # for i in reversed(range(ha1.depth)):
        #     t1_set = ha1.trans_with_depth[i]
        #     t2_set = ha2.trans_with_depth[i]
        #     # if last transition, just merge error modes
        #     # since there are no dynamics and invariants
        #     # for error modes
        #     if i == ha1.depth - 1:
        #         error_mode = ha.new_mode("error")
        #         for t1 in t1_set:
        #             merged_mode, is_agg = merge_mode(ha, t1.src, t2.src)
        #         # new_t1_trans = ha.new_transition(t1.name, t1.src, error_mode, freeze_counter=True)
        #         # new_t2_trans = ha.new_transition(t2.name, t2.src, error_mode)
        #         # if is_agg and isinstance(merged_mode, AggregatedMode):
        #         #     new_t1_trans.src = merged_mode
        #         #     new_t2_trans.src = merged_mode
        #
        #     # t1 = ha1.trans_with_depth[i]
        #     # t2 = ha2.trans_with_depth[i]
        #     # if t1.trg.dynamics == t2.trg.dynamics:
        #     #     ha2_subsume_ha1 = subsumption(t2.trg.invariant, t1.trg.invariant)
        #     #     ha1_subsume_ha2 = subsumption(t1.trg.invariant, t2.trg.invariant)
        #     #     if not ha2_subsume_ha1 and not ha1_subsume_ha2:
        #     #         print("cannot merge {} and {}".format(t1.trg.name, t2.trg.name))
        #     #         continue
        #     #     new_agg_mode = ha.new_mode("{}+{}".format(t1.trg.name, t2.trg.name), is_aggregated=True)
        #     #     if isinstance(new_agg_mode, AggregatedMode):
        #     #         new_agg_mode.add(t1)
        #     #         new_agg_mode.add(t2)
        #     #         new_agg_mode.set_dynamics(t1.trg.dynamics)
        #     #         if ha2_subsume_ha1:
        #     #             new_agg_mode.set_invariant(t1.trg.invariant)
        #     #         else:
        #     #             # ha1_subsume_ha2
        #     #             new_agg_mode.set_invariant(t2.trg.invariant)
        #     # else:
        #     #     old_t1_trg = ha.new_mode(t1.trg.name)
        #     #     old_t1_trg.set_dynamics(t1.trg.dynamics)
        #     #     old_t1_trg.set_invariant(t1.trg.invariant)
        #     #
        #     #     old_t2_trg = ha.new_mode(t2.trg.name)
        #     #     old_t2_trg.set_dynamics(t2.trg.dynamics)
        #     #     old_t2_trg.set_invariant(t2.trg.invariant)

    else:
        raise NotSupportedError("automata have different depths")

    return ha
