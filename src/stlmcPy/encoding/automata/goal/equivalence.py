from .graph import *
from .label import *


# pre and postfix equivalence
class PPEquivalence:
    def __init__(self):
        self._equiv_rel: List[Set[Node]] = list()
        self._ap_dict: Dict[Node, Set[Proposition]] = dict()
        self._clock_subst: Dict[Tuple[Node, Node], ClockSubstitution] = dict()

    def calc_initial_equivalence(self, graph: TableauGraph):
        self._prepare(graph)

        # ignore the first dummy node
        nodes = graph.get_nodes().copy()
        nodes.discard(graph.first_node())

        pairs = set(combinations(nodes, 2))

        # identity
        for n in nodes:
            self._clock_subst[(n, n)] = self._identity_clk_subst(n)

        for n1, n2 in pairs:
            # using the clk_subst, n2 is equivalent to n1
            clk_subst = self._label_eq(n1, n2)
            if clk_subst is not None:
                assert (n1, n2) not in self._clock_subst
                self._clock_subst[(n1, n2)] = clk_subst

        for n1, n2 in pairs:
            # if n1 and n2 are equivalent
            if (n1, n2) in self._clock_subst:
                found = False
                for n_set in self._equiv_rel:
                    possible = set(product([n1], n_set)).union(product(n_set, [n1]))
                    for p in possible:
                        if p in self._clock_subst:
                            n_set.update({n1, n2})
                            found = True
                            break

                if not found:
                    self._equiv_rel.append({n1, n2})
            else:
                found1, found2 = False, False
                for n_set in self._equiv_rel:
                    possible1 = set(product([n1], n_set)).union(product(n_set, [n1]))
                    possible2 = set(product([n2], n_set)).union(product(n_set, [n2]))
                    for p in possible1:
                        if p in self._clock_subst:
                            n_set.add(n1)
                            found1 = True
                            break

                    for p in possible2:
                        if p in self._clock_subst:
                            n_set.add(n2)
                            found2 = True
                            break

                if not found1:
                    self._equiv_rel.append({n1})

                if not found2:
                    self._equiv_rel.append({n2})

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

        # no need refinement
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

        # filter the pred nodes jump to the nodes in the splitter
        node1_jp_post = set(filter(lambda x: x.get_src() in splitter, node1_jp_post))
        node2_jp_post = set(filter(lambda x: x.get_src() in splitter, node2_jp_post))

        checked_jp1 = set()
        for jp1 in node1_jp_post:
            n_node1 = jp1.get_trg()
            for jp2 in node2_jp_post:
                n_node2 = jp2.get_trg()

                # need to consider jump conditions (with clock variable renaming)

                # case[0]: n_node2 is equivalent to n_node1 by a clock substitution
                # case[1]: n_node1 is equivalent to n_node2 by a clock substitution
                case = [(n_node1, n_node2) in self._clock_subst,
                        (n_node2, n_node1) in self._clock_subst]
                assert case[0] or case[1]

                if case[0]:
                    clk_subst = self._clock_subst[(n_node1, n_node2)]
                    jp_ap = [frozenset(jp1.get_ap()),
                             frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))]

                    # found equivalent jp2
                    if jp_ap[0] == jp_ap[1]:
                        checked_jp1.add(jp1)
                else:
                    clk_subst = self._clock_subst[(n_node2, n_node1)]
                    jp_ap = [frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp1.get_ap())),
                             frozenset(jp2.get_ap())]

                    # found equivalent jp2
                    if jp_ap[0] == jp_ap[1]:
                        checked_jp1.add(jp1)

        # should be refined
        if checked_jp1 != node1_jp_post:
            return False

        checked_jp2 = set()
        for jp2 in node2_jp_post:
            n_node2 = jp2.get_trg()
            for jp1 in node1_jp_post:
                n_node1 = jp1.get_trg()

                # need to consider jump conditions (with clock variable renaming)

                # case[0]: n_node2 is equivalent to n_node1 by a clock substitution
                # case[1]: n_node1 is equivalent to n_node2 by a clock substitution
                case = [(n_node1, n_node2) in self._clock_subst,
                        (n_node2, n_node1) in self._clock_subst]
                assert case[0] or case[1]

                if case[0]:
                    clk_subst = self._clock_subst[(n_node1, n_node2)]
                    jp_ap = [frozenset(jp1.get_ap()),
                             frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))]

                    # found equivalent jp2
                    if jp_ap[0] == jp_ap[1]:
                        checked_jp2.add(jp2)
                else:
                    clk_subst = self._clock_subst[(n_node2, n_node1)]
                    jp_ap = [frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp1.get_ap())),
                             frozenset(jp2.get_ap())]

                    # found equivalent jp2
                    if jp_ap[0] == jp_ap[1]:
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

        checked_jp1 = set()
        for jp1 in node1_jp_pre:
            n_node1 = jp1.get_src()
            for jp2 in node2_jp_pre:
                n_node2 = jp2.get_src()

                # need to consider jump conditions (with clock variable renaming)

                # case[0]: n_node2 is equivalent to n_node1 by a clock substitution
                # case[1]: n_node1 is equivalent to n_node2 by a clock substitution
                case = [(n_node1, n_node2) in self._clock_subst,
                        (n_node2, n_node1) in self._clock_subst]
                assert case[0] or case[1]

                if case[0]:
                    clk_subst = self._clock_subst[(n_node1, n_node2)]
                    jp_ap = [frozenset(jp1.get_ap()),
                             frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))]

                    # found equivalent jp2
                    if jp_ap[0] == jp_ap[1]:
                        checked_jp1.add(jp1)
                else:
                    clk_subst = self._clock_subst[(n_node2, n_node1)]
                    jp_ap = [frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp1.get_ap())),
                             frozenset(jp2.get_ap())]

                    # found equivalent jp2
                    if jp_ap[0] == jp_ap[1]:
                        checked_jp1.add(jp1)

        # should be refined
        if checked_jp1 != node1_jp_pre:
            return False

        checked_jp2 = set()
        for jp2 in node2_jp_pre:
            n_node2 = jp2.get_src()
            for jp1 in node1_jp_pre:
                n_node1 = jp1.get_src()

                # need to consider jump conditions (with clock variable renaming)

                # case[0]: n_node2 is equivalent to n_node1 by a clock substitution
                # case[1]: n_node1 is equivalent to n_node2 by a clock substitution
                case = [(n_node1, n_node2) in self._clock_subst,
                        (n_node2, n_node1) in self._clock_subst]
                assert case[0] or case[1]

                if case[0]:
                    clk_subst = self._clock_subst[(n_node1, n_node2)]
                    jp_ap = [frozenset(jp1.get_ap()),
                             frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp2.get_ap()))]

                    # found equivalent jp2
                    if jp_ap[0] == jp_ap[1]:
                        checked_jp2.add(jp2)
                else:
                    clk_subst = self._clock_subst[(n_node2, n_node1)]
                    jp_ap = [frozenset(map(lambda x: clk_subst.substitute(x),
                                           jp1.get_ap())),
                             frozenset(jp2.get_ap())]

                    # found equivalent jp2
                    if jp_ap[0] == jp_ap[1]:
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

    def _label_eq(self, node1: Node, node2: Node) -> Optional[ClockSubstitution]:
        ty_eq = [node1.is_initial() == node2.is_initial(),
                 node1.is_final() == node2.is_final()]

        if not all(ty_eq):
            return None

        # two states are equivalent modulo their clock variables
        assert node1 in self._ap_dict and node2 in self._ap_dict

        ap1, ap2 = self._ap_dict[node1], self._ap_dict[node2]

        if len(ap1) != len(ap2):
            return None

        # clock equivalence detection
        # 1) get clock pools of the goals
        # 1.1) if the pools' size differ, the goals are not equivalent
        p1, p2 = get_clock_pool(*ap1), get_clock_pool(*ap2)

        if len(p1) != len(p2):
            return None

        # calc hash for goal1 for efficiency
        c_goal1_hash, n_goal1_hash = hash(frozenset(ap1)), hash(frozenset(ap1))

        p1_o, p2_o_pool = tuple(p1), set(permutations(p2))

        for p2_o in p2_o_pool:
            assert isinstance(p2_o, Tuple)

            # possible clock mapping
            possible = set(zip(p1_o, p2_o))
            mapping = ClockSubstitution()
            for c1, c2 in possible:
                mapping.add(c2, c1)

            c_goal2_n = frozenset(map(lambda x: mapping.substitute(x), ap2))

            # if successfully find clock mapping for the current goals
            if c_goal1_hash == hash(c_goal2_n):
                return mapping

        return None

    def _identity_clk_subst(self, node: Node) -> ClockSubstitution:
        assert node in self._ap_dict

        ap = self._ap_dict[node]

        clk_subst = ClockSubstitution()
        for clk in get_clock_pool(*ap):
            clk_subst.add(clk, clk)
        return clk_subst


def _fresh_group_id():
    counter = 0
    while True:
        yield counter
        counter += 1
