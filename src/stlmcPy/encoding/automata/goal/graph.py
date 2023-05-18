from typing import FrozenSet

from .clock import *
from .label import *
from .optimizer import ContradictionChecker
from ....constraints.constraints import Real, Formula
from ....graph.graph import *
from ....util.printer import indented_str


class TableauGraph(Graph['Node', 'Jump']):
    def __init__(self, formula: Formula):
        Graph.__init__(self)
        self._formula = formula
        self._dummy_node = Node(set(), set(), set())
        self._label: Dict[Node, Label] = dict()
        self._matching_info: Dict[Node, ClockMatchingInfo] = dict()
        self._node_indexing: Dict[Tuple[hash, hash, hash], List[Node]] = dict()
        self.add_node(self._dummy_node)

    def first_node(self):
        # the first dummy node is used to make initial edges
        return self._dummy_node

    def get_nodes(self):
        return self.vertices

    def get_label(self, node: 'Node') -> Label:
        assert node in self._label
        return self._label[node]

    def add_node(self, node: 'Node'):
        assert node not in self._matching_info
        assert node not in self._node_indexing

        self.add_vertex(node)
        self._matching_info[node] = self._make_matching_info(node)

        indexing = self._make_indexing_info(node)
        if indexing in self._node_indexing:
            self._node_indexing[indexing].append(node)
        else:
            self._node_indexing[indexing] = [node]

    @classmethod
    def _make_matching_info(cls, node: 'Node') -> 'ClockMatchingInfo':
        inv = get_clock_pool(*node.invariant)
        cur, nxt = get_clock_pool(*node.cur_goals), get_clock_pool(*node.nxt_goals)
        node_clk_s = inv.union(cur).union(nxt)

        matching_info = ClockMatchingInfo(node_clk_s)

        for f in node.invariant:
            matching_info.add(f, "inv")

        for g in node.cur_goals:
            matching_info.add(g, "cur")

        for g in node.nxt_goals:
            matching_info.add(g, "nxt")

        return matching_info

    def _make_indexing_info(self, node: 'Node') -> Tuple[hash, hash, hash]:
        inv_idx = self._indexing_info(node.invariant)
        cur_idx = self._indexing_info(node.cur_goals)
        nxt_idx = self._indexing_info(node.nxt_goals)

        return hash(inv_idx), hash(cur_idx), hash(nxt_idx)

    @classmethod
    def _indexing_info(cls, f_s: Set[Formula]) -> FrozenSet[Formula]:
        indexing = set()
        for f in f_s:
            # time props
            open_close = isinstance(f, OCProposition)
            label_time_prop = isinstance(f, TimeProposition)
            clk_time_assn = isinstance(f, ClkAssn)
            up = isinstance(f, Up)
            updown = isinstance(f, UpDown)
            if not (open_close or label_time_prop or clk_time_assn or up or updown):
                indexing.add(f)
        return frozenset(indexing)

    @classmethod
    def make_node(cls, label: Label, is_initial=False) -> 'Node':
        return Node(label.state_cur, label.nxt, label.inv_assertion.difference(label.inv_forbidden),
                    is_initial, len(label.nxt) <= 0)

    @classmethod
    def make_jump(cls, src: 'Node', trg: 'Node', conditions: Set[Formula]) -> 'Jump':
        return Jump(src, trg, conditions)

    def remove_node(self, node: 'Node'):
        self.remove_vertex(node)

    def add_jump(self, jump: 'Jump'):
        self.add_edge(jump)

    def remove_jump(self, jump: 'Jump'):
        self.remove_edge(jump)

    def find_node(self, node: 'Node') -> Tuple[bool, Optional['Node'], Optional[ClockSubstitution]]:
        indexing_info = self._make_indexing_info(node)

        # if there is no indexing info, there is no matching node exists
        if indexing_info not in self._node_indexing:
            return False, None, None

        matching_info = self._make_matching_info(node)
        nodes = self._node_indexing[indexing_info]

        for n in nodes:
            if n == self.first_node():
                continue

            # both goals should be final or not final
            if n.is_final() != node.is_final():
                continue

            assert n in self._matching_info
            n_match = self._matching_info[n]

            clk_subst = n_match.match(matching_info)
            if clk_subst is not None:
                return True, n, clk_subst

        return False, None, None

    @classmethod
    def identity_clk_subst(cls, clk_s: Set[Real]) -> ClockSubstitution:
        identity = ClockSubstitution()
        for clk in clk_s:
            identity.add(clk, clk)
        return identity

    @classmethod
    def get_state_clocks(cls, node: 'Node') -> Set[Real]:
        c_clk = get_clock_pool(*node.cur_goals)
        # n_clk = get_clock_pool(*node.nxt_goals)
        inv_clk = get_clock_pool(*node.invariant)
        return c_clk.union(inv_clk)

    @classmethod
    def jump_write_clocks(cls, jp_c: Set[Formula]) -> Set[Real]:
        write_clk = set()
        for f in jp_c:
            if isinstance(f, ClkAssn):
                write_clk.add(f.clock)
        return write_clk

    @classmethod
    def jump_read_clocks(cls, jp_c: Set[Formula]) -> Set[Real]:
        read_clk = set()
        for f in jp_c:
            if isinstance(f, TimeProposition):
                read_clk.add(f.clock)
        return read_clk

    def open_label(self, node: 'Node', label: Label):
        assert node not in self._label
        self._label[node] = label

    def remove_unreachable(self):
        self._remove_unreachable_to_final()
        self._remove_unreachable_from_initial()

    def _remove_unreachable_from_initial(self):
        f_ns = set(filter(lambda x: x.is_initial(), self.get_nodes()))
        new_states, reachable = f_ns.copy(), f_ns.copy()

        while len(new_states) > 0:
            temp = set()
            for s in new_states:
                temp.update(self.get_next_vertices(s))
            new_states = temp.difference(reachable)
            reachable.update(new_states)

        unreachable = self.get_nodes().difference(reachable)
        for s in unreachable:
            self.remove_node(s)

    def _remove_unreachable_to_final(self):
        f_ns = set(filter(lambda x: x.is_final(), self.get_nodes()))
        new_states, reachable = f_ns.copy(), f_ns.copy()

        while len(new_states) > 0:
            temp = set()
            for s in new_states:
                temp.update(self.get_pred_vertices(s))
            new_states = temp.difference(reachable)
            reachable.update(new_states)

        unreachable = self.get_nodes().difference(reachable)
        for s in unreachable:
            self.remove_node(s)

    def remove_self_loop(self):
        jp_s = get_node_jumps(self)
        for jp in jp_s:
            if jp.get_src() == jp.get_trg():
                self.remove_edge(jp)

    def __repr__(self):
        node_str = "node:\n{}".format("\n".join([str(node) for node in self.vertices]))
        edges_str = "jump:\n{}".format("\n".join([str(jp) for jp in get_node_jumps(self)]))
        return "\n".join([node_str, edges_str])


class Node:
    def __init__(self, cur_goals: Set[Formula], nxt_goals: Set[Formula], invariant: Set[Formula],
                 is_initial=False, is_final=False):
        self.cur_goals, self.nxt_goals = cur_goals.copy(), nxt_goals.copy()
        self.invariant = invariant.copy()

        self._is_initial = is_initial
        self._is_final = is_final

    def __repr__(self):
        goal_str = [list(), list()]
        for g in self.cur_goals:
            goal_str[0].append(indented_str(str(g), 6))

        for g in self.nxt_goals:
            goal_str[1].append(indented_str(str(g), 6))

        inv_str = list()
        for f in self.invariant:
            inv_str.append(indented_str(str(f), 6))

        id_info = indented_str("id: {}".format(hash(self)), 4)
        is_initial = indented_str("initial: {}".format(self._is_initial), 4)
        is_final = indented_str("final: {}".format(self._is_final), 4)
        inv = indented_str("inv:\n{}".format("\n".join(inv_str)), 4)
        c_goal_info = indented_str("cur goal:\n{}".format("\n".join(goal_str[0])), 4)
        n_goal_info = indented_str("nxt goal:\n{}".format("\n".join(goal_str[1])), 4)

        return "( Node\n{}\n)".format("\n".join([id_info, is_initial, is_final, inv, c_goal_info, n_goal_info]))

    def is_final(self):
        return self._is_final

    def is_initial(self):
        return self._is_initial


class Jump(Edge[Node]):
    def __init__(self, src: Node, trg: Node, ap: Set[Formula]):
        self._src, self._trg = src, trg
        self._ap = frozenset(ap)
        self._hash = hash((src, trg, self._ap))

    def get_ap(self):
        return self._ap

    def __hash__(self):
        return self._hash

    def __eq__(self, other):
        return hash(self) == hash(other)

    def get_src(self) -> Node:
        return self._src

    def get_trg(self) -> Node:
        return self._trg

    def __repr__(self):
        jp_ap = indented_str("ap:\n{}".format("\n".join([indented_str(str(f), 6) for f in self._ap])), 4)
        jp_body = indented_str("{} -> {}".format(hash(self._src), hash(self._trg)), 4)

        return "( jump \n{}\n{}\n  )".format(jp_ap, jp_body)


def get_node_jumps(graph: TableauGraph) -> Set[Jump]:
    jp_s: Set[Jump] = set()
    for node in graph.get_nodes():
        jp_s.update(graph.get_next_edges(node))

    return jp_s


class JumpContradictionChecker:
    def __init__(self):
        self._checker = ContradictionChecker()

    def is_contradiction(self, jp: Jump) -> bool:
        return self._checker.is_contradiction(*self._translate(jp.get_ap()))

    @classmethod
    def _translate(cls, f_set: FrozenSet[Formula]) -> Set[Formula]:
        r = set()
        for f in f_set:
            tf = translate_time_goal(f)
            if tf is not None:
                r.add(tf)
        return r


class ClockMatchingInfo:
    def __init__(self, clocks: Set[Real]):
        self._matching_info: Dict[Tuple[str, hash, hash, str], List[List[Real]]] = dict()
        self._clocks = clocks.copy()

    def add(self, goal: Formula, ty: str):
        info = _matching_info(goal, ty)

        if info is None:
            return

        if info in self._matching_info:
            self._matching_info[info].append(_get_matching_clocks(goal))
        else:
            self._matching_info[info] = [_get_matching_clocks(goal)]

    def match(self, other: 'ClockMatchingInfo') -> Optional[ClockSubstitution]:
        assert isinstance(other, ClockMatchingInfo)

        if len(self._clocks) != len(other._clocks):
            return None

        k_c = set(self._matching_info.keys())
        # information must be equal
        if k_c != set(other._matching_info.keys()):
            return None

        subst_s = _clock_match(list(k_c), 0, other._matching_info, self._matching_info, dict())

        # if nothing found
        if len(subst_s) <= 0:
            return None

        subst = max(subst_s, key=lambda x: _subst_score(x))

        clk_subst = ClockSubstitution()
        for k in subst:
            clk_subst.add(k, subst[k])

        # filled the remaining matching
        k_s, v_s = set(), set()
        for k in subst:
            k_s.add(k)
            v_s.add(subst[k])

        k_s = list(self._clocks.difference(k_s))
        v_s = list(other._clocks.difference(v_s))

        assert len(k_s) == len(v_s)

        for c1, c2 in list(zip(k_s, v_s)):
            clk_subst.add(c1, c2)

        return clk_subst

    def __repr__(self):
        m = "\n".join(["{} ---> {}".format(k, self._matching_info[k]) for k in self._matching_info])
        return "clock matching\n{}\n".format(m)


def _clock_match(positions: List[Tuple[str, hash, hash, str]], index: int,
                 match1: Dict[Tuple[str, hash, hash, str], List[List[Real]]],
                 match2: Dict[Tuple[str, hash, hash, str], List[List[Real]]],
                 subst: Dict[Real, Real]) -> List[Dict[Real, Real]]:
    if len(positions) <= index:
        # check validity assertion
        # e.g., invalid case: c1 --> c2, c3 --> c2
        # u = set()
        # for k in subst:
        #     if subst[k] in u:
        #         return list()
        #     else:
        #         u.add(subst[k])
        return [subst]

    pos = positions[index]
    p_clk1, p_clk2 = match1[pos], match2[pos]

    if len(p_clk1) != len(p_clk2):
        return list()

    p_clk2_order = list(map(lambda x: list(x), permutations(p_clk2)))

    found = list()
    for trial, clk2_set in enumerate(p_clk2_order):
        n_subst = _match_test(subst, p_clk1, clk2_set)
        if n_subst is None:
            continue

        m = _clock_match(positions, index + 1, match1, match2, n_subst)
        if m is not None:
            found.extend(m)

    return found


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

    for c1, c2 in list(zip(c1_set, c2_set)):
        # conflict
        if c1 in subst:
            if not variable_equal(subst[c1], c2):
                return None
            else:
                continue
        new_subst[c1] = c2
    return new_subst


def _subst_score(subst: Dict[Real, Real]) -> int:
    score = 0
    for k in subst:
        if variable_equal(k, subst[k]):
            score += 1
    return score


@singledispatch
def _matching_info(goal: Formula, ty: str) -> Optional[Tuple[str, hash, hash, str]]:
    return None


@_matching_info.register(Up)
def _(goal: Up, ty: str) -> Optional[Tuple[str, hash, hash, str]]:
    return goal.temporal, hash(goal.interval), hash(goal.formula), ty


@_matching_info.register(UpDown)
def _(goal: UpDown, ty: str) -> Optional[Tuple[str, hash, hash, str]]:
    return "{}{}".format(goal.temporal1, goal.temporal2), hash(goal.interval), hash(goal.formula), ty


@_matching_info.register(TimeProposition)
def _(goal: TimeProposition, ty: str) -> Optional[Tuple[str, hash, hash, str]]:
    return "T_{{{},{}}}".format(goal.temporal, goal.name_s), hash(goal.interval), 0, ty


@_matching_info.register(ClkAssn)
def _(goal: ClkAssn, ty: str) -> Optional[Tuple[str, hash, hash, str]]:
    return "assn", hash(goal.value), 0, ty


@_matching_info.register(Open)
def _(goal: Open, ty: str) -> Optional[Tuple[str, hash, hash, str]]:
    return "open", 0, 0, ty


@_matching_info.register(Close)
def _(goal: Close, ty: str) -> Optional[Tuple[str, hash, hash, str]]:
    return "close", 0, 0, ty


@_matching_info.register(OpenClose)
def _(goal: OpenClose, ty: str) -> Optional[Tuple[str, hash, hash, str]]:
    return "oc", 0, 0, ty


@singledispatch
def _get_matching_clocks(goal: Formula) -> List[Real]:
    raise Exception("wrong matching goal")


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
