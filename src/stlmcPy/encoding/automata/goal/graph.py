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
        self._labels: Dict[Node, Set[Label]] = dict()
        self._matching_info: Dict[Node, ClockMatchingInfo] = dict()
        self._node_indexing: Dict[FrozenSet[Proposition], List[Node]] = dict()
        self.add_node(self._dummy_node)

    def first_node(self):
        # the first dummy node is used to make initial edges
        return self._dummy_node

    def get_nodes(self):
        return self.vertices

    def get_labels(self, node: 'Node') -> Set[Label]:
        assert node in self.get_nodes()
        if node not in self._labels:
            return set()
        return self._labels[node].copy()

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
    def _make_matching_info(cls, node: 'Node') -> ClockMatchingInfo:
        matching_info = ClockMatchingInfo()
        for g in node.cur_goals:
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
    def make_jump(cls, src: 'Node', trg: 'Node', label: Label) -> 'Jump':
        return Jump(src, trg, label.transition_cur)

    def remove_node(self, node: 'Node'):
        self.remove_vertex(node)

    def add_jump(self, jump: 'Jump'):
        self.add_edge(jump)

    def remove_jump(self, jump: 'Jump'):
        self.remove_edge(jump)

    def find_node(self, node: 'Node') -> Tuple[bool, Optional['Node'],
                                               Optional[ClockSubstitution]]:
        matching_info = self._make_matching_info(node)
        indexing_info = self._make_indexing_info(node)
        node_goals = [node.cur_goals, node.nxt_goals]

        # split clock and others
        node_clk_s = (filter_clock_goals(*node_goals[0]),
                      filter_clock_goals(*node_goals[1]))
        node_other = [node_goals[0].difference(node_clk_s[0]),
                      node_goals[1].difference(node_clk_s[1])]

        # if there is no indexing info, there is no matching node exists
        if indexing_info not in self._node_indexing:
            return False, None, None

        nodes = self._node_indexing[indexing_info]

        for n in nodes:
            if n == self.first_node():
                continue

            assert n in self._matching_info
            n_match = self._matching_info[n]

            n_goals = [n.cur_goals, n.nxt_goals]

            # split clock and others
            clk_s = (filter_clock_goals(*n_goals[0]),
                     filter_clock_goals(*n_goals[1]))
            other = [n_goals[0].difference(clk_s[0]),
                     n_goals[1].difference(clk_s[1])]

            clk_subst = n_match.match(matching_info)
            if clk_subst is None:
                continue
            else:
                eq = [n.is_final() == node.is_final(),
                      other[0] == node_other[0],
                      other[1] == node_other[1]]
                if all(eq) and self._clock_eq(clk_subst, clk_s, node_clk_s):
                    return True, n, clk_subst

        return False, None, None

    @classmethod
    def _clock_eq(cls, clk_subst: ClockSubstitution,
                  clk_goal1: Tuple[Set[Formula], Set[Formula]],
                  clk_goal2: Tuple[Set[Formula], Set[Formula]]) -> bool:
        c_goal1, n_goal1 = clk_goal1[0], clk_goal1[1]
        c_goal2, n_goal2 = clk_goal2[0], clk_goal2[1]

        goal1_hash = [hash(frozenset(c_goal1)), hash(frozenset(n_goal1))]
        goal2_hash = [hash(frozenset(map(lambda x: clk_subst.substitute(x), c_goal2))),
                      hash(frozenset(map(lambda x: clk_subst.substitute(x), n_goal2)))]

        return goal1_hash[0] == goal2_hash[0] and goal1_hash[1] == goal2_hash[1]

    @classmethod
    def update_label_clock(cls, label: Label, clk_subst: ClockSubstitution):
        # make transition conditions
        t_c, clk_reset = set(), clk_subst.clock_assn()
        for f in label.transition_cur:
            # case1) apply clock renaming to reset conditions
            if isinstance(f, ClkAssn):
                # assert that there are no variables on the RHS of the resets
                assert not isinstance(f.value, Variable)
                t_c.add(clk_subst.substitute(f))
            else:
                # case2) add substitution resets for the other conditions
                t_c.add(f)
                t_c.update(clk_reset)

        cur = [{clk_subst.substitute(f) for f in label.state_cur}, t_c]

        nxt = [{clk_subst.substitute(f) for f in label.state_nxt},
               {clk_subst.substitute(f) for f in label.transition_nxt}]

        cur_assertion = {clk_subst.substitute(a) for a in label.cur_assertion}
        cur_forbidden = {clk_subst.substitute(f) for f in label.cur_forbidden}
        nxt_assertion = {clk_subst.substitute(a) for a in label.nxt_assertion}
        nxt_forbidden = {clk_subst.substitute(f) for f in label.nxt_forbidden}
        inv_assertion = {clk_subst.substitute(inv) for inv in label.inv_assertion}
        inv_forbidden = {clk_subst.substitute(inv) for inv in label.inv_forbidden}

        # calc max clock index
        clk_s = get_clock_pool(*cur[0]).union(get_clock_pool(*cur[1]))
        clk_s.update(get_clock_pool(*nxt[0]).union(get_clock_pool(*nxt[1])))

        # if there is no clock
        if len(clk_s) <= 0:
            max_clock = 0
        else:
            max_clock = max({clock_index(clk) for clk in clk_s})

        return Label(cur[0], cur[1], nxt[0], nxt[1],
                     cur_assertion, cur_forbidden, nxt_assertion, nxt_forbidden,
                     inv_assertion, inv_forbidden, max_clock)

    @classmethod
    def update_type_hint_clocks(cls, clk_subst: ClockSubstitution, *ty_hints):
        return set(map(lambda x: clk_subst.substitute(x), ty_hints))

    def open_labels(self, node: 'Node', *labels):
        if node in self._labels:
            self._labels[node].update({lb for lb in labels})
        else:
            self._labels[node] = {lb for lb in labels}

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
