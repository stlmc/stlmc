from .graph import *
from .label import *


# pre and postfix equivalence
class PPEquivalence:
    def __init__(self):
        self._equiv_rel: List[Set[Node]] = list()
        self._ap_dict: Dict[Node, Set[Proposition]] = dict()
        self._clock_subst: Dict[Tuple[Node, Node], Optional[ClockSubstitution]] = dict()
        self._clock_matching: Dict[Node, ClockMatchingInfo] = dict()

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

        k = node1, node2
        # get clock substitution
        n1_m, n2_m = self._clock_matching[node1], self._clock_matching[node2]
        if k in self._clock_subst:
            return self._clock_subst[k]
        else:
            self._clock_subst[k] = n1_m.match(n2_m)
            return self._clock_subst[k]

    def calc_initial_equivalence(self, graph: TableauGraph):
        self._prepare(graph)

        # ignore the first dummy node
        nodes = graph.get_nodes().copy()
        nodes.discard(graph.first_node())

        # make clock matching
        for node in nodes:
            assert node not in self._clock_matching
            self._clock_matching[node] = self._make_clock_matching(node)

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

        for node in equiv:
            equiv_c = equiv[node]
            equiv_c.add(node)

            self._equiv_rel.append(equiv_c)

    def refine(self, graph: TableauGraph):
        pre = self._equiv_rel.copy()
        while True:
            parts = set(permutations(range(len(self._equiv_rel)), 2))
            for index1, index2 in parts:
                nodes, splitter = self._equiv_rel[index1], self._equiv_rel[index2]
                r_s = self._refine(nodes, splitter, graph)

                if r_s is not None:
                    self._equiv_rel.remove(nodes)
                    for rf in r_s:
                        self._equiv_rel.append(rf)

            if self._equiv_rel == pre:
                break

            pre = self._equiv_rel.copy()

        # refine graph
        for n_set in self._equiv_rel:
            r_n = n_set.pop()

            # remove vertex and copy its jumps
            for n in n_set:
                jp_p_s = graph.get_pred_edges(n)
                jp_n_s = graph.get_next_edges(n)

                for jp in jp_p_s:
                    new_jp = Jump(jp.get_src(), r_n, jp.get_ap())
                    graph.add_jump(new_jp)

                for jp in jp_n_s:
                    new_jp = Jump(r_n, jp.get_trg(), jp.get_ap())
                    graph.add_jump(new_jp)

                graph.remove_node(n)

    def _refine(self, nodes: Set[Node], splitter: Set[Node],
                graph: TableauGraph) -> Optional[List[Set[Node]]]:
        waiting = nodes.copy()

        # id counter of new sets
        id_counter = _fresh_group_id()

        # group id dictionary
        # assume that all the nodes are in the same group
        g_d: Dict[Node, int] = dict()
        initial_id = next(id_counter)
        for node in nodes:
            g_d[node] = initial_id

        while len(waiting) > 0:
            # pick a node
            n = waiting.pop()
            for node in waiting:
                refine_cond = [not self._post_checking(n, node, splitter, graph),
                               not self._pre_checking(n, node, splitter, graph)]

                # need to refine
                if all(refine_cond):
                    # assign a new group
                    g_d[node] = next(id_counter)
                else:
                    # n and node should be in the same group
                    g_d[node] = g_d[n]

        # make new sets
        groups: Dict[int, Set[Node]] = dict()
        for node in g_d:
            g_id = g_d[node]
            if g_id in groups:
                groups[g_id].add(node)
            else:
                groups[g_id] = {node}

        # no refinement
        if len(groups) <= 1:
            return None

        # otherwise return refined sets
        return [groups[g_id] for g_id in groups]

    # bisimulation post equivalence checking
    # return true when the nodes are bisimilar (i.e., no need to refine)
    # otherwise return false
    def _post_checking(self, node1: Node, node2: Node,
                       splitter: Set[Node], graph: TableauGraph) -> bool:
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
        # print("  post checking")
        # print("    jp1 {}, jp2 {}".format(len(node1_jp_post), len(node2_jp_post)))

        checked_jp1 = set()
        for jp1 in node1_jp_post:
            n_node1 = jp1.get_trg()
            for jp2 in node2_jp_post:
                n_node2 = jp2.get_trg()

                if len(jp1.get_ap()) != len(jp2.get_ap()):
                    continue

                # get clock substitution
                clk_subst = self._get_clock_subst(n_node1, n_node2)

                # need to consider jump conditions (with clock variable renaming)
                if clk_subst is None:
                    jp2_ap = jp2.get_ap()
                else:
                    jp2_ap = frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))

                # found equivalent jp2
                if jp1.get_ap() == jp2_ap:
                    checked_jp1.add(jp1)

        # should be refined
        if checked_jp1 != node1_jp_post:
            return False

        checked_jp2 = set()
        for jp2 in node2_jp_post:
            n_node2 = jp2.get_trg()
            for jp1 in node1_jp_post:
                n_node1 = jp1.get_trg()

                if len(jp2.get_ap()) != len(jp1.get_ap()):
                    continue

                # need to consider jump conditions (with clock variable renaming)
                clk_subst = self._get_clock_subst(n_node2, n_node1)
                if clk_subst is None:
                    jp1_ap = jp1.get_ap()
                else:
                    jp1_ap = frozenset(map(lambda x: clk_subst.substitute(x),
                                       jp1.get_ap()))

                # found equivalent jp2
                if jp2.get_ap() == jp1_ap:
                    checked_jp2.add(jp2)

        # should be refined
        if checked_jp2 != node2_jp_post:
            return False

        return True

    # bisimulation pre equivalence checking
    # return true when the nodes are bisimilar (i.e., no need to refine)
    # otherwise return false
    def _pre_checking(self, node1: Node, node2: Node,
                      splitter: Set[Node], graph: TableauGraph) -> bool:
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
            n_node1 = jp1.get_src()
            for jp2 in node2_jp_pre:
                n_node2 = jp2.get_src()

                if len(jp1.get_ap()) != len(jp2.get_ap()):
                    continue

                # get clock substitution
                clk_subst = self._get_clock_subst(n_node1, n_node2)

                # need to consider jump conditions (with clock variable renaming)
                if clk_subst is None:
                    jp2_ap = jp2.get_ap()
                else:
                    jp2_ap = frozenset(map(lambda x: clk_subst.substitute(x),
                                       jp2.get_ap()))

                # found equivalent jp2
                if jp1.get_ap() == jp2_ap:
                    checked_jp1.add(jp1)

        # should be refined
        if checked_jp1 != node1_jp_pre:
            return False

        checked_jp2 = set()
        for jp2 in node2_jp_pre:
            n_node2 = jp2.get_src()
            for jp1 in node1_jp_pre:
                n_node1 = jp1.get_src()

                if len(jp2.get_ap()) != len(jp1.get_ap()):
                    continue

                # need to consider jump conditions (with clock variable renaming)
                clk_subst = self._get_clock_subst(n_node2, n_node1)

                if clk_subst is None:
                    jp1_ap = jp1.get_ap()
                else:
                    jp1_ap = frozenset(map(lambda x: clk_subst.substitute(x),
                                       jp1.get_ap()))

                # found equivalent jp2
                if jp2.get_ap() == jp1_ap:
                    checked_jp2.add(jp2)

        # should be refined
        if checked_jp2 != node2_jp_pre:
            return False

        return True

    def _prepare(self, graph: TableauGraph):
        # ignore the first dummy node
        nodes = graph.get_nodes().copy()
        nodes.discard(graph.first_node())

        for node in nodes:
            assert node not in self._ap_dict

            self._ap_dict[node] = set(filter(lambda x: isinstance(x, Proposition), node.cur_goals))

    def _label_eq(self, node1: Node, node2: Node) -> bool:
        ty_eq = [node1.is_initial() == node2.is_initial(),
                 node1.is_final() == node2.is_final()]

        if not all(ty_eq):
            return False

        assert node1 in self._ap_dict and node2 in self._ap_dict
        ap1, ap2 = self._ap_dict[node1], self._ap_dict[node2]

        return len(ap1) == len(ap2)


def _fresh_group_id():
    counter = 0
    while True:
        yield counter
        counter += 1
