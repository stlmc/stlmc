from itertools import permutations, product
from typing import FrozenSet

from .clock import *
from .label import *
from ....constraints.constraints import Real, Formula
from ....graph.graph import *
from ....util.printer import indented_str


class TableauGraph(Graph['Node', 'Jump']):
    def __init__(self, formula: Formula):
        Graph.__init__(self)
        self._formula = formula
        self._dummy_node = Node(set())
        self._labels: Dict[Node, Set[Label]] = dict()
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
        self.add_vertex(node)

    @classmethod
    def make_node(cls, label: Label, is_initial=False) -> 'Node':
        return Node(label.state_cur, is_initial, len(label.nxt) <= 0)

    @classmethod
    def make_jumps(cls, src: 'Node', trg: 'Node', label: Label) -> Set['Jump']:
        oc_s = set(filter(lambda x: isinstance(x, OpenClose), label.transition_cur))
        other = label.transition_cur.difference(oc_s)

        type_s = list()
        for oc in oc_s:
            assert isinstance(oc, OpenClose)
            type_s.append([Open(oc.var), Close(oc.var)])

        jp_s = set()
        for t in list(product(*type_s)):
            jp_s.add(Jump(src, trg, other.union(t)))

        return jp_s

    def remove_node(self, node: 'Node'):
        self.remove_vertex(node)

    def add_jump(self, jump: 'Jump'):
        self.add_edge(jump)

    def remove_jump(self, jump: 'Jump'):
        self.remove_edge(jump)

    def find_node(self, node: 'Node') -> Tuple[bool, Optional['Node'],
                                               Optional[ClockSubstitution]]:
        # ignore top formula and clk resets
        node_goals = self._ignore_top_formula(*node.goals)

        # split clock and others
        node_clk_s = filter_clock_goals(*node_goals)
        node_other = node_goals.difference(node_clk_s)

        for n in self.get_nodes():
            eq = [n.is_final() == node.is_final(),
                  n.is_initial() == node.is_initial()]
            # ignore top formula and clk resets
            n_goals = self._ignore_top_formula(*n.goals)

            # split clock and others
            clk_s = filter_clock_goals(*n_goals)
            other = n_goals.difference(clk_s)

            clk_eq, clk_subst = self._clock_eq(clk_s, node_clk_s)

            if clk_eq and other == node_other and eq[0]:
                return True, n, clk_subst
        return False, None, None

    @classmethod
    def _clock_eq(cls, goal1: Set[Formula],
                  goal2: Set[Formula]) -> Tuple[bool, Optional[ClockSubstitution]]:
        # clock equivalence detection
        # 1) get clock pools of the goals
        # 1.1) if the pools' size differ, the goals are not equivalent
        p1, p2 = get_clock_pool(*goal1), get_clock_pool(*goal2)

        if len(p1) != len(p2):
            return False, None

        # 2) (assume that the pools are equal) make mappings
        # Dict[Real, Set[str]]
        clk_ty_map1 = make_clk_type_mapping(*goal1)

        # 3) check if the mappings are equal
        # fix ordering of p1 and calculate all possible orderings of p2
        p1_o, p2_o_pool = tuple(p1), set(permutations(p2))

        for p2_o in p2_o_pool:
            assert isinstance(p2_o, Tuple)

            # possible clock mapping
            possible = set(zip(p1_o, p2_o))
            mapping = ClockSubstitution()
            for c1, c2 in possible:
                mapping.add(c2, c1)

            goals = set(map(lambda x: mapping.substitute(x), goal2))
            clk_ty_map2 = make_clk_type_mapping(*goals)

            # if successfully find clock mapping
            if clk_ty_map1 == clk_ty_map2:
                return True, mapping

        # otherwise
        return False, None

    def _ignore_top_formula(self, *goals) -> Set[Formula]:
        return set(filter(lambda x: hash(x) != hash(self._formula), goals))

    @classmethod
    def update_label_clock(cls, label: Label, clk_subst: ClockSubstitution):
        cur = [{clk_subst.substitute(f) for f in label.state_cur},
               {clk_subst.substitute(f) for f in label.transition_cur}]

        nxt = [{clk_subst.substitute(f) for f in label.state_nxt},
               {clk_subst.substitute(f) for f in label.transition_nxt}]

        return Label(cur[0], cur[1], nxt[0], nxt[1])

    @classmethod
    def update_type_hint_clocks(cls, clk_subst: ClockSubstitution, *ty_hints):
        return set(map(lambda x: clk_subst.substitute(x), ty_hints))

    def open_labels(self, node: 'Node', *labels):
        if node in self._labels:
            self._labels[node].update({lb for lb in labels})
        else:
            self._labels[node] = {lb for lb in labels}

    def __repr__(self):
        node_str = "node:\n{}".format("\n".join([str(node) for node in self.vertices]))
        edges_str = "jump:\n{}".format("\n".join([str(jp) for jp in get_node_jumps(self)]))
        return "\n".join([node_str, edges_str])


class Node:
    def __init__(self, goals: Set[Formula], is_initial=False, is_final=False):
        self.goals = goals.copy()
        self._hash = hash((frozenset(goals), is_initial, is_final))

        self._is_initial = is_initial
        self._is_final = is_final

    def __repr__(self):
        goal_str_list = list()
        for g in self.goals:
            goal_str_list.append(indented_str(str(g), 6))

        id_info = indented_str("id: {}".format(hash(self)), 4)
        is_initial = indented_str("initial: {}".format(self._is_initial), 4)
        is_final = indented_str("final: {}".format(self._is_final), 4)
        goal_info = indented_str("goal:\n{}".format("\n".join(goal_str_list)), 4)

        return "( Node\n{}\n)".format("\n".join([id_info, is_initial, is_final, goal_info]))

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


def _is_final_label(label: Label):
    return len(label.nxt) == 0


def _find_reachable(graph: TableauGraph) -> Set[Node]:
    # set finals as reachable nodes
    reach, un_reach = set(filter(lambda n: n.is_final(), graph.get_nodes())), set()

    # prepare rest of the nodes
    waiting = graph.get_nodes().difference(reach)
    while len(waiting) > 0:
        for node in waiting:
            n_succ = graph.get_next_vertices(node)
            # else at least one successor is reachable
            if len(n_succ.intersection(reach)) > 0:
                reach.add(node)

            # all successors are unreachable
            if n_succ.issubset(un_reach):
                un_reach.add(node)

        waiting.difference_update(reach)
        waiting.difference_update(un_reach)

    return reach
