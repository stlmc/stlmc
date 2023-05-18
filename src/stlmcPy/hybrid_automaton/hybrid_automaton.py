from typing import Set, Dict, Tuple

from ..constraints.constraints import *
from ..exception.exception import NotSupportedError
from ..graph.graph import *
from ..util.printer import indented_str, p_string


class HybridAutomaton(Graph['Mode', 'Transition']):
    def __init__(self):
        Graph.__init__(self)
        self.init: Set[Formula] = set()

    def add_init(self, *inits):
        for init in inits:
            self.init.add(init)

    def get_modes(self):
        return self.vertices.copy()

    def add_mode(self, mode: 'Mode'):
        self.add_vertex(mode)

    def remove_mode(self, mode: 'Mode'):
        self.remove_vertex(mode)

    def add_transition(self, transition: 'Transition'):
        self.add_edge(transition)

    def remove_transition(self, transition: 'Transition'):
        self.remove_edge(transition)

    def remove_unreachable(self):
        f_ns = set(filter(lambda x: x.is_initial(), self.get_modes()))
        new_states, reachable = f_ns.copy(), f_ns.copy()

        while len(new_states) > 0:
            temp = set()
            for s in new_states:
                temp.update(self.get_next_vertices(s))
            new_states = temp.difference(reachable)
            reachable.update(new_states)

        unreachable = self.get_modes().difference(reachable)
        for s in unreachable:
            self.remove_mode(s)

    def get_bound_box(self) -> 'BoundBox':
        bound_box = BoundBox()
        queue = self.init.copy()
        while len(queue) > 0:
            const = queue.pop()
            if isinstance(const, MultinaryFormula):
                queue.update(const.children)
            elif isinstance(const, Proposition):
                bound_box.put(const)
            else:
                raise NotSupportedError("error in initial conditions")
        return bound_box

    def __repr__(self):
        init_m, final_m, total_m = set(), set(), set()
        for m in self.vertices:
            total_m.add(str(m.id))
            if m.is_initial():
                init_m.add(str(m.id))
            if m.is_final():
                final_m.add(str(m.id))

        init_str = "\n".join([indented_str("mode {}".format(m_id), 4) for m_id in init_m])
        final_str = "\n".join([indented_str("mode {}".format(m_id), 4) for m_id in final_m])
        total_str = "\n".join([indented_str("mode {}".format(m_id), 4) for m_id in total_m])

        ha_str = "hybrid automaton\n"
        ha_str += indented_str("initial modes:\n{}\n".format(init_str), 2)
        ha_str += indented_str("final modes:\n{}\n".format(final_str), 2)
        ha_str += indented_str("total modes:\n{}\n".format(total_str), 2)
        ha_str += indented_str("Modes:\n", 2)
        ha_str += "\n".join([indented_str(str(m), 2) for m in self.vertices])
        ha_str += "\n"

        jp_s = set()
        for mode in self.vertices:
            jp_s = jp_s.union(self.get_next_edges(mode))

        ha_str += indented_str("Transitions:\n", 2)

        jp_str = set()
        for jp in jp_s:
            jp_str.add(indented_str(str(jp), 2))

        ha_str += "\n".join(jp_str)
        return ha_str


class Mode:
    def __init__(self, identifier: int):
        self.dynamics: Dict[Variable, Expr] = dict()
        self.invariant: Set[Formula] = set()
        self.id = identifier

        self._is_initial = False
        self._is_final = False

    def add_dynamic(self, *dyns):
        for v, e in dyns:
            if v in self.dynamics:
                raise Exception("variable {} already has dynamics".format(v))

            self.dynamics[v] = e

    def add_invariant(self, *invariants):
        for inv in invariants:
            self.invariant.add(inv)

    def set_as_final(self):
        self._is_final = True

    def set_as_non_final(self):
        self._is_final = False

    def set_as_initial(self):
        self._is_initial = True

    def set_as_non_initial(self):
        self._is_initial = False

    def is_final(self):
        return self._is_final

    def is_initial(self):
        return self._is_initial

    def __repr__(self):
        dyn_body = "\n".join([indented_str("{} = {}".format(v, self.dynamics[v]), 6) for v in self.dynamics])
        dyn_str = indented_str("dyn:\n{}".format(dyn_body), 4)

        inv_body = "\n".join([p_string(inv, 6) for inv in self.invariant])
        inv_str = indented_str("inv:\n{}".format(inv_body), 4)

        return "( mode {}\n{}\n{}\n  )".format(self.id, dyn_str, inv_str)


class Transition(Edge[Mode]):
    def __init__(self, src: Mode, trg: Mode):
        self._src, self._trg = src, trg
        self.guard: Set[Formula] = set()
        self.reset: Set[Tuple[Variable, Formula]] = set()

    def get_src(self) -> Mode:
        return self._src

    def get_trg(self) -> Mode:
        return self._trg

    def add_guard(self, *guards):
        for guard in guards:
            self.guard.add(guard)

    def add_reset(self, *resets):
        for v, f in resets:
            self.reset.add((v, f))

    def __repr__(self):
        guard_body = "\n".join([p_string(g, 6) for g in self.guard])
        guard_str = indented_str("guard:\n{}".format(guard_body), 4)

        reset_body = "\n".join([indented_str("{} := {}".format(v, f), 6) for v, f in self.reset])
        reset_str = indented_str("reset:\n{}".format(reset_body), 4)

        jp_body = indented_str("{} -> {}".format(self._src.id, self._trg.id), 4)

        return "( jump \n{}\n{}\n{}\n  )".format(guard_str, reset_str, jp_body)


def make_fresh_jump(mode1: Mode, mode2: Mode, **consts) -> Transition:
    jp = Transition(mode1, mode2)

    if "guards" in consts:
        jp.add_guard(*consts["guards"])

    if "resets" in consts:
        jp.add_reset(*consts["resets"])

    return jp


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

    def __repr__(self):
        v_s = set()
        v_s.update(self.lower_closed.keys())
        v_s.update(self.lower_opened.keys())
        v_s.update(self.upper_closed.keys())
        v_s.update(self.upper_opened.keys())

        bb_str = list()
        for v in v_s:
            v_str = "{}=".format(v)
            if v in self.lower_closed:
                v_str += "[{}".format(self.lower_closed[v])

            if v in self.lower_opened:
                v_str += "({}".format(self.lower_opened[v])

            if v in self.upper_closed:
                v_str += ",{}]".format(self.upper_closed[v])

            if v in self.upper_opened:
                v_str += ",{})".format(self.upper_opened[v])
            bb_str.append(v_str)

        return "\n".join(bb_str)

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
            raise NotSupportedError("does not have lower ({})".format(key))

        if not is_in_upper_closed and not is_in_upper_opened:
            raise NotSupportedError("does not have upper ({})".format(key))

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

    def put(self, const: Formula):
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
