from typing import FrozenSet

from .graph import *
from .label import *


# pre and postfix equivalence
class PPEquivalence:
    def __init__(self):
        self._ap_dict: Dict[Node, Set[Proposition]] = dict()
        self._clock_subst: Dict[Tuple[Node, Node], Optional[ClockSubstitution]] = dict()
        self._clock_matching: Dict[Node, ClockMatchingInfo] = dict()

    def reduce(self, graph: TableauGraph):
        self._clear()
        # ignore the first dummy node
        nodes = graph.get_nodes().copy()
        nodes.discard(graph.first_node())

        # make clock matching and ap dictionary information
        for node in nodes:
            assert node not in self._ap_dict
            assert node not in self._clock_matching
            self._ap_dict[node] = set(filter(lambda x: isinstance(x, Proposition), node.cur_goals))
            self._clock_matching[node] = self._make_clock_matching(node)

        # make initial pre and post equivalence partition
        partition = self._calc_initial_equivalence(nodes)

        iter = 0
        while True:
            iter += 1
            print("reduction iteration #{}".format(iter))
            old_partition = partition.copy()
            old_v = len(graph.get_nodes())

            # calculate pre- and post-partition and merge them
            pre_partition = self._refine_partition(old_partition, graph)
            post_partition = self._refine_partition(old_partition, graph, is_post=True)
            partition = self._merge_partition(pre_partition, post_partition)
            self._partition_assertion(partition, graph)

            # reduce graph using the partition
            partition = self._reduce_graph(graph, partition)
            v = len(graph.get_nodes())

            if old_v == v:
                break

    def _calc_initial_equivalence(self, nodes: Set[Node]) -> Set[FrozenSet[Node]]:
        equiv: Dict[Node, Set[Node]] = dict()
        for node in nodes:
            # nodes that are already calculated
            covered = set(equiv.keys())
            for n in equiv:
                covered.update(equiv[n])

            to_be_checked = nodes.difference(covered)

            for n in to_be_checked:
                if self._label_eq(node, n):
                    if node in equiv:
                        equiv[node].add(n)
                    else:
                        equiv[node] = {n}

        equiv_rel = set()
        for node in equiv:
            equiv_c = equiv[node]
            equiv_c.add(node)

            equiv_rel.add(frozenset(equiv_c))

        return equiv_rel

    def _refine_partition(self, partition: Set[FrozenSet[Node]],
                          graph: TableauGraph, is_post=False) -> Set[FrozenSet[Node]]:
        equiv_rel = partition.copy()
        while True:
            old_rel = equiv_rel.copy()
            for splitter in old_rel:
                eq_rel = set()
                for nodes in equiv_rel:
                    r_s = self._refine(set(nodes), splitter, graph, is_post)
                    for rf in r_s:
                        eq_rel.add(rf)

                equiv_rel = eq_rel

            if old_rel == equiv_rel:
                break

        return equiv_rel

    @classmethod
    def _merge_partition(cls, equiv_rel1: Set[FrozenSet[Node]],
                         equiv_rel2: Set[FrozenSet[Node]]) -> Set[FrozenSet[Node]]:
        equiv_graph = EquivGraph()

        # make equiv graph
        id_gen = _fresh_group_id()
        id_dict: Dict[FrozenSet[Node], int] = dict()
        n_dict: Dict[int, FrozenSet[Node]] = dict()

        # make nodes
        for eq in equiv_rel1.union(equiv_rel2):
            g_id = next(id_gen)
            n_dict[g_id], id_dict[eq] = eq, g_id
            equiv_graph.add_eq_node(g_id)

        # add edges
        possible = set(product(equiv_rel1, equiv_rel2))
        for eq1, eq2 in possible:
            if len(eq1.intersection(eq2)) > 0:
                s_id, t_id = id_dict[eq1], id_dict[eq2]
                equiv_graph.add_eq_edge(s_id, t_id)

        # calculate connected components
        eg_ccs = equiv_graph.connected_component()

        merged_equiv_rel = set()
        for cc in eg_ccs:
            equiv_class = set()
            for eq_node in cc:
                equiv_class.update(n_dict[eq_node.id])
            merged_equiv_rel.add(frozenset(equiv_class))

        return merged_equiv_rel

    @classmethod
    def _partition_assertion(cls, partition: Set[FrozenSet[Node]], graph: TableauGraph):
        nodes = graph.get_nodes().copy()
        nodes.discard(graph.first_node())

        univ = set()
        for eq_class in partition:
            univ.update(eq_class)

        assert nodes == univ

    @classmethod
    def _reduce_graph(cls, graph: TableauGraph,
                      equiv_rel: Set[FrozenSet]) -> Set[FrozenSet[Node]]:
        new_equiv_rel = set()
        # refine graph
        for n_set in equiv_rel:
            # pick a node
            e_set = list(sorted(n_set, key=lambda x: len(graph.get_pred_edges(x))))
            r_n = e_set.pop(0)

            # add it to the new equivalent class
            new_equiv_rel.add(frozenset({r_n}))

            # remove vertex and copy its jumps
            for n in e_set:
                jp_p_s = graph.get_pred_edges(n)
                jp_n_s = graph.get_next_edges(n)

                for jp in jp_p_s:
                    new_jp = Jump(jp.get_src(), r_n, jp.get_ap())
                    graph.add_jump(new_jp)

                for jp in jp_n_s:
                    new_jp = Jump(r_n, jp.get_trg(), jp.get_ap())
                    graph.add_jump(new_jp)

                graph.remove_node(n)
        return new_equiv_rel

    def _refine(self, nodes: Set[Node], splitter: FrozenSet[Node],
                graph: TableauGraph, is_post=False) -> Set[FrozenSet[Node]]:

        tot_len = len(nodes)
        waiting = nodes.copy()
        # pick an initial node
        p_n = waiting.pop()

        # group id dictionary
        groups: Dict[Node, Set[Node]] = dict()
        groups[p_n] = {p_n}

        while True:
            covered = set(groups.keys())
            for n in groups:
                covered.update(groups[n])

            waiting = nodes.difference(covered)
            if len(waiting) <= 0:
                break
            node = waiting.pop()
            need_refine = True
            for n in groups:
                if is_post:
                    no_need_to_refine = self._post_checking(node, n, splitter, graph)
                else:
                    no_need_to_refine = self._pre_checking(node, n, splitter, graph)

                # no need to refine
                if no_need_to_refine:
                    groups[n].add(node)
                    need_refine = False
                    break

            if need_refine:
                assert node not in groups
                groups[node] = {node}

        r_tot_len = 0
        for g_id in groups:
            r_tot_len += len(groups[g_id])
            if nodes == groups[g_id]:
                assert len(groups) == 1

        assert tot_len == r_tot_len
        # return refined sets
        return {frozenset(groups[g_id]) for g_id in groups}

    # bisimulation post equivalence checking
    # return true when the nodes are bisimilar (i.e., no need to refine)
    # otherwise return false
    def _post_checking(self, node1: Node, node2: Node,
                       splitter: FrozenSet[Node], graph: TableauGraph) -> bool:
        # get post edges
        node1_jp_post = graph.get_next_edges(node1)
        node2_jp_post = graph.get_next_edges(node2)

        # filter the post nodes jump to the nodes in the splitter
        node1_jp_post = set(filter(lambda x: x.get_trg() in splitter, node1_jp_post))
        node2_jp_post = set(filter(lambda x: x.get_trg() in splitter, node2_jp_post))

        # simple refinement condition
        s_c = [len(node1_jp_post) == 0 and len(node2_jp_post) > 0,
               len(node1_jp_post) > 0 and len(node2_jp_post) == 0]

        if len(node1_jp_post) == 0 and len(node2_jp_post) == 0:
            return True

        if any(s_c):
            return False

        # need to consider jump conditions (with clock variable renaming)
        clk_subst = self._get_clock_subst(node1, node2)

        checked_jp1 = set()
        for jp1 in node1_jp_post:
            for jp2 in node2_jp_post:
                if len(jp1.get_ap()) != len(jp2.get_ap()):
                    continue

                if clk_subst is None:
                    jp2_ap = jp2.get_ap()
                else:
                    jp2_ap = frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))

                # found equivalent jp2
                if jp1.get_ap() == jp2_ap:
                    checked_jp1.add(jp1)
                    break

        # should be refined
        if checked_jp1 != node1_jp_post:
            return False

        checked_jp2 = set()
        for jp2 in node2_jp_post:
            for jp1 in node1_jp_post:
                if len(jp2.get_ap()) != len(jp1.get_ap()):
                    continue

                if clk_subst is None:
                    jp2_ap = jp2.get_ap()
                else:
                    jp2_ap = frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))

                # found equivalent jp2
                if jp1.get_ap() == jp2_ap:
                    checked_jp2.add(jp2)
                    break

        # should be refined
        if checked_jp2 != node2_jp_post:
            return False

        return True

    # bisimulation pre equivalence checking
    # return true when the nodes are bisimilar (i.e., no need to refine)
    # otherwise return false
    def _pre_checking(self, node1: Node, node2: Node,
                      splitter: FrozenSet[Node], graph: TableauGraph) -> bool:
        # get pre edges
        node1_jp_pre = graph.get_pred_edges(node1)
        node2_jp_pre = graph.get_pred_edges(node2)

        # filter the pred nodes jump to the nodes in the splitter
        node1_jp_pre = set(filter(lambda x: x.get_src() in splitter, node1_jp_pre))
        node2_jp_pre = set(filter(lambda x: x.get_src() in splitter, node2_jp_pre))

        # simple refinement condition
        s_c = [len(node1_jp_pre) == 0 and len(node2_jp_pre) > 0,
               len(node1_jp_pre) > 0 and len(node2_jp_pre) == 0]

        if len(node1_jp_pre) == 0 and len(node2_jp_pre) == 0:
            return True

        if any(s_c):
            return False

        checked_jp1 = set()
        for jp1 in node1_jp_pre:
            for jp2 in node2_jp_pre:
                if len(jp1.get_ap()) != len(jp2.get_ap()):
                    continue

                # need to consider jump conditions (with clock variable renaming)
                clk_subst = self._get_clock_subst(jp1.get_src(), jp2.get_src())
                if clk_subst is None:
                    jp2_ap = jp2.get_ap()
                else:
                    jp2_ap = frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))

                # found equivalent jp2
                if jp1.get_ap() == jp2_ap:
                    checked_jp1.add(jp1)
                    break

        # should be refined
        if checked_jp1 != node1_jp_pre:
            return False

        checked_jp2 = set()
        for jp2 in node2_jp_pre:
            for jp1 in node1_jp_pre:
                if len(jp2.get_ap()) != len(jp1.get_ap()):
                    continue

                # need to consider jump conditions (with clock variable renaming)
                clk_subst = self._get_clock_subst(jp1.get_src(), jp2.get_src())
                if clk_subst is None:
                    jp2_ap = jp2.get_ap()
                else:
                    jp2_ap = frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))

                # found equivalent jp2
                if jp2_ap == jp1.get_ap():
                    checked_jp2.add(jp2)
                    break

        # should be refined
        if checked_jp2 != node2_jp_pre:
            return False

        return True

    def _label_eq(self, node1: Node, node2: Node) -> bool:
        ty_eq = [node1.is_initial() == node2.is_initial(),
                 node1.is_final() == node2.is_final()]

        if not all(ty_eq):
            return False

        assert node1 in self._ap_dict and node2 in self._ap_dict
        ap1, ap2 = self._ap_dict[node1], self._ap_dict[node2]

        if len(ap1) != len(ap2):
            return False

        return ap1 == ap2

    def _clear(self):
        self._ap_dict.clear()
        self._clock_subst.clear()
        self._clock_matching.clear()

    def _make_clock_matching(self, node: 'Node') -> ClockMatchingInfo:
        assert node in self._ap_dict

        matching_info = ClockMatchingInfo()

        for g in node.cur_goals:
            matching_info.add_cur(g)

        for g in node.nxt_goals:
            matching_info.add_nxt(g)

        return matching_info

    def _get_clock_subst(self, node1: Node, node2: Node) -> Optional[ClockSubstitution]:
        assert node1 in self._clock_matching and node2 in self._clock_matching
        # get clock substitution to rename node2 to node1
        k = node1, node2
        # get clock substitution
        n1_m, n2_m = self._clock_matching[node1], self._clock_matching[node2]
        if k in self._clock_subst:
            return self._clock_subst[k]
        else:
            self._clock_subst[k] = n1_m.match(n2_m)
            return self._clock_subst[k]


def _fresh_group_id():
    counter = 0
    while True:
        yield counter
        counter += 1


class EquivGraph(Graph['EquivNode', 'EquivEdge']):
    def __init__(self):
        super().__init__()

    def add_eq_node(self, node_id: int):
        self.add_vertex(EquivNode(node_id))

    def add_eq_edge(self, src: int, trg: int):
        src_n, trg_n = EquivNode(src), EquivNode(trg)
        assert src_n in self.vertices and trg_n in self.vertices

        jp1, jp2 = EquivEdge(src_n, trg_n), EquivEdge(trg_n, src_n)
        self.add_edge(jp1)
        self.add_edge(jp2)

    def connected_component(self):
        seen = set()
        connected_component = list()
        for node in self.vertices:
            connected = _dfs(node, seen, self)
            if len(connected) > 0:
                connected_component.append(connected)

        return connected_component


class EquivNode:
    def __init__(self, equiv_class: int):
        self.id = equiv_class

    def __hash__(self):
        return hash(self.id)

    def __eq__(self, other):
        return self.__hash__() == hash(other)

    def __repr__(self):
        return str(self.id)


class EquivEdge(Edge[EquivNode]):
    def __init__(self, src: EquivNode, trg: EquivNode):
        self._src, self._trg = src, trg

    def __hash__(self):
        return hash((self._src, self._trg))

    def __eq__(self, other):
        return self.__hash__() == hash(other)

    def __repr__(self):
        return "{} --> {}".format(self._src, self._trg)

    def get_src(self) -> EquivNode:
        return self._src

    def get_trg(self) -> EquivNode:
        return self._trg


def _dfs(node: EquivNode, seen: Set[EquivNode], graph: EquivGraph) -> Set[EquivNode]:
    if node in seen:
        return set()

    connected = {node}
    seen.add(node)
    next_nodes = graph.get_next_vertices(node)
    for n in next_nodes:
        connected.update(_dfs(n, seen, graph))

    return connected