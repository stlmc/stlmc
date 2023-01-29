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
        self._node_indexing: Dict[FrozenSet[Proposition], List[Node]] = dict()
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
        matching_info = ClockMatchingInfo()
        cur = node.invariant.union(node.cur_goals)
        for g in cur:
            matching_info.add_cur(g)

        for g in node.nxt_goals:
            matching_info.add_nxt(g)

        return matching_info

    @classmethod
    def _make_indexing_info(cls, node: 'Node') -> FrozenSet[Proposition]:
        indexing = set()
        for f in node.cur_goals:
            # time props
            open_close = isinstance(f, OCProposition)
            label_time_prop = isinstance(f, TimeProposition)
            clk_time_assn = isinstance(f, ClkAssn)
            if isinstance(f, Proposition):
                if not (open_close or label_time_prop or clk_time_assn):
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

    def find_node(self, node: 'Node') -> Tuple[bool, Optional['Node'],
                                               Optional[ClockSubstitution]]:
        indexing_info = self._make_indexing_info(node)

        # if there is no indexing info, there is no matching node exists
        if indexing_info not in self._node_indexing:
            return False, None, None

        matching_info = self._make_matching_info(node)

        # split clock and others
        c_node_clk, c_node_other = self._split_goals(node.cur_goals)
        n_node_clk, n_node_other = self._split_goals(node.nxt_goals)

        nodes = self._node_indexing[indexing_info]

        for n in nodes:
            if n == self.first_node():
                continue

            assert n in self._matching_info
            n_match = self._matching_info[n]

            # split clock and others
            c_clk_s, c_other = self._split_goals(n.cur_goals)
            n_clk_s, n_other = self._split_goals(n.nxt_goals)

            clk_subst = n_match.match(matching_info)
            if clk_subst is None:
                continue

            # both goals should be
            # i) final or not be final at the same time
            is_final = n.is_final() == node.is_final()

            # ii) non-time goals are the same for the current and next
            c_non_time_eq = c_node_other == c_other
            n_non_time_eq = n_node_other == n_other
            non_time_eq = c_non_time_eq and n_non_time_eq

            # iii) time goals should be equivalent with respect to the clock renaming
            c_time_eq = self._clock_eq(clk_subst, c_clk_s, c_node_clk)
            n_time_eq = self._clock_eq(clk_subst, n_clk_s, n_node_clk)
            time_eq = c_time_eq and n_time_eq

            # iv) invariant should be equivalent with respect to the clock renaming
            inv_eq = self._clock_eq(clk_subst, n.invariant, node.invariant)
            if is_final and non_time_eq and time_eq and inv_eq:
                # mapped_clk = clk_subst.vars()
                # cur_clk_s = self.get_state_clocks(n)

                # make an identity mapping for the rest of the variables
                # missed_clk = cur_clk_s.difference(mapped_clk)
                # for clk in missed_clk:
                #     clk_subst.add(clk, clk)
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

    @classmethod
    def _split_goals(cls, goals: Set[Formula]) -> Tuple[Set[Formula], Set[Formula]]:
        # split time and non-time goals
        clk_goals = filter_clock_goals(*goals)
        other_goals = goals.difference(clk_goals)

        return clk_goals, other_goals

    @classmethod
    def _clock_eq(cls, clk_subst: ClockSubstitution,
                  goals1: Set[Formula], goals2: Set[Formula]) -> bool:
        goal1_hash = hash(frozenset(goals1))
        goal2_hash = hash(frozenset(map(lambda x: clk_subst.substitute(x), goals2)))
        return goal1_hash == goal2_hash

    def open_label(self, node: 'Node', label: Label):
        assert node not in self._label
        self._label[node] = label

    def remove_unreachable(self):
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

        subst = clock_match(list(k_c), other._matching_info_cur, self._matching_info_cur, dict())
        if subst is None:
            return None

        k_n = set(self._matching_info_nxt.keys())
        if k_n != set(other._matching_info_nxt.keys()):
            return None

        subst = clock_match(list(k_n), other._matching_info_nxt, self._matching_info_nxt, subst)
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

