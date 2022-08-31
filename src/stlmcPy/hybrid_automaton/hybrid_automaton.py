from itertools import product
from typing import Set, Tuple, Dict

from ..constraints.aux.operations import get_vars
from ..constraints.constraints import *
from ..exception.exception import NotSupportedError
from ..util.printer import indented_str, p_string

Constraint = Formula


class HybridAutomaton:
    def __init__(self, name: str):
        self.name: str = name
        self.modes: Set[Mode] = set()
        self.transitions: Set[Transition] = set()

        # for special purpose
        self.final_modes: Set[Mode] = set()
        self.initial_modes: Set[Mode] = set()

        self.initial_conditions: Set[Constraint] = set()
        self.final_conditions: Set[Constraint] = set()

    def get_vars(self) -> Set[Variable]:
        var_set = set()
        for mode in self.modes:
            for (var, exp) in mode.dynamics:
                # add left hand variable
                var_set.add(var)

                # add variables in exp
                exp_var_set = get_vars(exp)
                var_set = var_set.union(exp_var_set)

            for inv in mode.invariant:
                inv_var_set = get_vars(inv)
                var_set = var_set.union(inv_var_set)

        for transition in self.transitions:
            for guard in transition.guard:
                var_set = var_set.union(get_vars(guard))

            for le, ri in transition.reset:
                var_set.add(le)
                var_set = var_set.union(get_vars(ri))

        return var_set

    def get_bound_bound(self) -> 'BoundBox':
        bound_box = BoundBox()
        queue = self.initial_conditions.copy()
        while len(queue) > 0:
            const = queue.pop()
            if isinstance(const, MultinaryFormula):
                queue.update(set(const.children))
            elif isinstance(const, Proposition):
                bound_box.put(const)
            else:
                raise NotSupportedError("error in initial conditions")
        return bound_box

    def add_mode(self, name: str) -> 'Mode':
        mode = Mode(name, self)
        self.modes.add(mode)
        return mode

    def remove_mode(self, mode: 'Mode'):
        self.modes.discard(mode)

    def mark_final(self, mode: 'Mode'):
        assert mode in self.modes
        self.final_modes.add(mode)

    def mark_initial(self, mode: 'Mode'):
        assert mode in self.modes
        self.initial_modes.add(mode)

    def add_transition(self, name: str, src: 'Mode', trg: 'Mode') -> 'Transition':
        trans = Transition(name, src, trg, self)
        self.transitions.add(trans)
        src.outgoing.add(trans)
        trg.incoming.add(trans)
        return trans

    def __repr__(self):
        exact_name = self.name
        if len(exact_name) > 20:
            exact_name = "{} ...".format(exact_name[:20])

        init_str = "\n".join([indented_str(m.name, 4) for m in self.initial_modes])
        final_str = "\n".join([indented_str(m.name, 4) for m in self.final_modes])

        ha_str = "hybrid automaton ({})\n".format(exact_name)
        ha_str += indented_str("initial:\n{}\n".format(init_str), 2)
        ha_str += indented_str("final:\n{}\n".format(final_str), 2)
        ha_str += indented_str("Modes:\n", 2)
        ha_str += "\n".join([indented_str(str(m), 2) for m in self.modes])

        for i, trans in enumerate(self.transitions):
            if i == 0:
                ha_str += "\n  Transitions:\n  {}\n".format(trans)
            elif i < len(self.transitions) - 1:
                ha_str += "  {}\n".format(trans)
            else:
                ha_str += "  {}".format(trans)
        return ha_str


class Mode:
    def __init__(self, name, ha: HybridAutomaton):
        self.incoming: Set[Transition] = set()
        self.outgoing: Set[Transition] = set()

        self._dynamics: Set[Tuple[Variable, Expr]] = set()
        self._invariant: Set[Constraint] = set()

        self.ha = ha
        self.name = name

    def __hash__(self):
        return hash(id(self))

    def __eq__(self, other):
        return self.__hash__() == other.__hash__()

    @property
    def dynamics(self):
        return self._dynamics

    def set_dynamic(self, *dyns):
        for dyn in dyns:
            self._dynamics.add(dyn)

    def remove_dynamic(self, *dyns):
        for dyn in dyns:
            self._dynamics.discard(dyn)

    @property
    def invariant(self) -> Set[Formula]:
        return self._invariant

    def set_invariant(self, *invariants):
        for inv in invariants:
            self._invariant.add(inv)

    def remove_invariant(self, *invariants):
        for inv in invariants:
            self._invariant.discard(inv)

    def belongs_to(self) -> HybridAutomaton:
        return self.ha

    def __repr__(self):
        if self.ha is None:
            ha_name = "n/a"
        else:
            ha_name = self.ha.name

        if len(ha_name) > 20:
            simple_ha = "{} ...".format(ha_name[:20])

        mode_name = self.name
        if len(mode_name) > 20:
            mode_name = "{} ...".format(mode_name[:20])

        name = indented_str("name: {}, ha: {}".format(mode_name, ha_name), 4)
        dyn_body = "\n".join([indented_str("{} = {}".format(v, e), 6) for v, e in self.dynamics])
        dyn_str = indented_str("dyn:\n{}".format(dyn_body), 4)

        inv_body = "\n".join([p_string(inv, 6) for inv in self.invariant])
        inv_str = indented_str("inv:\n{}".format(inv_body), 4)

        return "( mode \n{}\n{}\n{}\n  )".format(name, dyn_str, inv_str)


class Transition:
    def __init__(self, name: str, src: Mode, trg: Mode, ha: HybridAutomaton):
        self.ha = ha
        self.name = name

        self.src = src
        self.trg = trg

        self.guard: Set[Constraint] = set()
        self.reset: Set[Tuple[Variable, Formula]] = set()

    def set_guard(self, *guards):
        for guard in guards:
            self.guard.add(guard)

    def remove_guard(self, *guards):
        for guard in guards:
            self.guard.discard(guard)

    def set_reset(self, *resets):
        for reset in resets:
            self.reset.add(reset)

    def remove_reset(self, *resets):
        for reset in resets:
            self.reset.discard(reset)

    def belongs_to(self) -> HybridAutomaton:
        return self.ha

    def __hash__(self):
        return hash(id(self))

    def __eq__(self, other):
        return self.__hash__() == other.__hash__()

    def __repr__(self):
        ha_name = self.ha.name
        if len(ha_name) > 20:
            ha_name = "{} ...".format(ha_name[:20])

        trans_name = self.name
        if len(trans_name) > 20:
            trans_name = "{} ...".format(trans_name[:20])

        name = indented_str("name: {}, ha: {}".format(trans_name, ha_name), 4)
        guard_body = "\n".join([p_string(g, 6) for g in self.guard])
        guard_str = indented_str("guard:\n{}".format(guard_body), 4)

        reset_body = "\n".join([indented_str("{} := {}".format(v, f), 6) for v, f in self.reset])
        reset_str = indented_str("reset:\n{}".format(reset_body), 4)

        jp_body = indented_str("{} -> {}".format(self.src.name, self.trg.name), 4)

        return "( jump \n{}\n{}\n{}\n{}\n  )".format(name, guard_str, reset_str, jp_body)


def composition(ha1: HybridAutomaton, ha2: HybridAutomaton) -> HybridAutomaton:
    ha = HybridAutomaton("composed_ha_{}_{}".format(ha1.name, ha2.name))

    ha1vars = ha1.get_vars()
    ha2vars = ha2.get_vars()
    v_s = ha1vars.union(ha2vars)

    ha.initial_conditions.update(ha1.initial_conditions)
    ha.initial_conditions.update(ha2.initial_conditions)

    candidate_modes: Set[Tuple[Mode, Mode]] = set(product(ha1.modes, ha2.modes))
    uid_dict: Dict[Mode, int] = dict()
    mode_dict: Dict[Tuple[Mode, Mode], Mode] = dict()

    for uid, (mode1, mode2) in enumerate(candidate_modes):
        is_mode1_initial = mode1 in ha1.initial_modes
        is_mode2_initial = mode2 in ha2.initial_modes

        is_mode1_final = mode1 in ha1.final_modes
        is_mode2_final = mode2 in ha2.final_modes

        mode = ha.add_mode("m_{}".format(uid))
        mode_dict[(mode1, mode2)] = mode
        uid_dict[mode] = uid

        mode.set_dynamic(*mode1.dynamics)
        mode.set_dynamic(*mode2.dynamics)

        mode.set_invariant(*mode1.invariant)
        mode.set_invariant(*mode2.invariant)

        if is_mode1_initial and is_mode2_initial:
            ha.mark_initial(mode)

        if is_mode1_final and is_mode2_final:
            ha.mark_final(mode)

    for pair in candidate_modes:
        (mode1, mode2) = pair
        mode_src = mode_dict[pair]

        trans1_exist = len(mode1.outgoing) > 0
        trans2_exist = len(mode2.outgoing) > 0

        if trans1_exist:
            for trans1 in mode1.outgoing:
                trg_key = (trans1.trg, mode2)
                assert trg_key in mode_dict
                mode_trg = mode_dict[trg_key]

                transition = ha.add_transition("t_{}_{}".format(id(mode_src), id(mode_trg)), mode_src, mode_trg)

                transition.set_guard(*trans1.guard)
                transition.set_reset(*[(v, v) for v in v_s])
                transition.set_reset(*trans1.reset)

        if trans2_exist:
            for trans2 in mode2.outgoing:
                trg_key = (mode1, trans2.trg)
                assert trg_key in mode_dict
                mode_trg = mode_dict[trg_key]

                transition = ha.add_transition("t_{}_{}".format(id(mode_src), id(mode_trg)), mode_src, mode_trg)
                for g in trans2.guard:
                    transition.set_guard(g)

                for r in trans2.reset:
                    transition.set_reset(r)

                # set identity reset
                for v in ha1vars.difference(ha2vars):
                    transition.set_reset((v, v))

    # assert no redundant mode exists
    for mode in ha.modes.copy():
        if len(mode.incoming) == 0 and len(mode.outgoing) == 0:
            assert mode not in ha.initial_modes or mode not in ha.final_modes

    return ha


class BoundBox:
    # (variable, real value), (real value, variable)
    vr = 0
    rv = 1

    # error
    err = 2

    # type
    leq = 3
    lt = 4
    geq = 5
    gt = 6
    eq = 7

    def __init__(self):
        self.lower_closed: Dict[Real, RealVal] = dict()
        self.lower_opened: Dict[Real, RealVal] = dict()

        self.upper_closed: Dict[Real, RealVal] = dict()
        self.upper_opened: Dict[Real, RealVal] = dict()

    def __getitem__(self, item):
        assert isinstance(item, Real)
        # alias of get
        return self.get(item)

    def __contains__(self, item):
        assert isinstance(item, Real)
        is_in_lower_closed = item in self.lower_closed
        is_in_lower_opened = item in self.lower_opened
        is_in_upper_closed = item in self.upper_closed
        is_in_upper_opened = item in self.upper_opened

        if not is_in_lower_closed and not is_in_lower_opened:
            # raise NotSupportedError("not in the bound box")
            return False

        if not is_in_upper_closed and not is_in_upper_opened:
            # raise NotSupportedError("not in the bound box")
            return False

        # should only be in one of lower or upper
        if is_in_lower_opened == is_in_lower_closed:
            raise NotSupportedError("bound box corrupted")
        if is_in_upper_opened == is_in_upper_closed:
            raise NotSupportedError("bound box corrupted")

        return True

    def get(self, key: Real) -> Interval:
        assert isinstance(key, Real)
        is_in_lower_closed = key in self.lower_closed
        is_in_lower_opened = key in self.lower_opened
        is_in_upper_closed = key in self.upper_closed
        is_in_upper_opened = key in self.upper_opened

        if not is_in_lower_closed and not is_in_lower_opened:
            raise NotSupportedError("not in bound box")

        if not is_in_upper_closed and not is_in_upper_opened:
            raise NotSupportedError("not in bound box")

        # should only be in one of these
        assert is_in_lower_opened != is_in_lower_closed
        assert is_in_upper_opened != is_in_upper_closed

        if is_in_lower_closed and is_in_upper_closed:
            return Interval(True, self.lower_closed[key], self.upper_closed[key], True)
        if is_in_lower_closed and is_in_upper_opened:
            return Interval(True, self.lower_closed[key], self.upper_opened[key], False)
        if is_in_lower_opened and is_in_upper_closed:
            return Interval(False, self.lower_opened[key], self.upper_closed[key], True)
        if is_in_lower_opened and is_in_upper_opened:
            return Interval(False, self.lower_opened[key], self.upper_opened[key], False)

        raise NotSupportedError("cannot make an interval")

    def put(self, const: Constraint):
        # check if correct
        op_type = BoundBox.err
        # get type first
        if isinstance(const, Leq):
            op_type = BoundBox.leq
        if isinstance(const, Lt):
            op_type = BoundBox.lt
        if isinstance(const, Geq):
            op_type = BoundBox.geq
        if isinstance(const, Gt):
            op_type = BoundBox.gt
        if isinstance(const, Eq):
            op_type = BoundBox.eq

        # type checking ... for sure
        assert op_type != BoundBox.err

        val_type = BoundBox.err

        if isinstance(const.left, Real) and isinstance(const.right, RealVal):
            val_type = BoundBox.vr
        elif isinstance(const.left, RealVal) and isinstance(const.right, Real):
            val_type = BoundBox.rv

        assert val_type != BoundBox.err

        # variable >= value or variable > value
        # variable <= value or variable < value
        # variable = value or value = variable
        if val_type == BoundBox.vr:
            if op_type == BoundBox.leq or op_type == BoundBox.lt:
                container_dict: Dict[int, Dict] = {BoundBox.leq: self.upper_closed, BoundBox.lt: self.upper_opened}
                container = container_dict[op_type]
                # upper type
                # variable <= value or variable < value
                if const.left in container:
                    if float(container[const.left].value) >= float(const.right.value):
                        container[const.left] = const.right
                else:
                    container[const.left] = const.right

            elif op_type == BoundBox.geq or op_type == BoundBox.gt:
                container_dict: Dict[int, Dict] = {BoundBox.geq: self.lower_closed, BoundBox.gt: self.lower_opened}
                container = container_dict[op_type]

                # lower type
                # variable >= value or variable > value
                if const.left in container:
                    if float(container[const.left].value) <= float(const.right.value):
                        container[const.left] = const.right
                else:
                    container[const.left] = const.right

            else:
                # variable = value
                if const.left not in self.lower_closed and const.left not in self.upper_closed:
                    self.lower_closed[const.left] = const.right
                    self.upper_closed[const.left] = const.right
                else:
                    raise NotSupportedError("cannot determine which value should bound box have")

        else:
            # value < variable type ...
            if op_type == BoundBox.leq or op_type == BoundBox.lt:
                container_dict: Dict[int, Dict] = {BoundBox.leq: self.lower_closed, BoundBox.lt: self.lower_opened}
                container = container_dict[op_type]
                # lower type
                # value < variable or value <= variable
                if const.right in container:
                    if float(container[const.right].value) <= float(const.left.value):
                        container[const.right] = const.left
                else:
                    container[const.right] = const.left

            elif op_type == BoundBox.geq or op_type == BoundBox.gt:
                container_dict: Dict[int, Dict] = {BoundBox.geq: self.upper_closed, BoundBox.gt: self.upper_opened}
                container = container_dict[op_type]

                # upper type
                # value >= variable or value > variable
                if const.right in container:
                    if float(container[const.right].value) >= float(const.left.value):
                        container[const.right] = const.left
                else:
                    container[const.right] = const.left

            else:
                # value = variable
                if const.right not in self.lower_closed and const.right not in self.upper_closed:
                    self.lower_closed[const.right] = const.left
                    self.upper_closed[const.right] = const.left
                else:
                    raise NotSupportedError("cannot determine which value should bound box have")
