from .graph import *
from .label import *


# pre and postfix equivalence
class PPEquivalence:
    def __init__(self):
        self._jump_clock_matching: Dict[Jump, ClockMatchingInfo] = dict()
        self._node_indexing: Dict[FrozenSet[Proposition], List[Node]] = dict()
        self._node_clock_goals: Dict[Node, Set[Formula]] = dict()
        self._node_none_clk_goals: Dict[Node, Set[Formula]] = dict()
        self._node_aps: Dict[Node, Set[Formula]] = dict()
        self._node_clocks: Dict[Node, Set[Real]] = dict()

    def reduce(self, graph: TableauGraph):
        self._clear()

        self._calc_node_info(graph)

        iter = 0
        while True:
            iter += 1
            print("reduction iteration #{}".format(iter))
            old_v = graph.get_nodes().copy()
            old_e = get_node_jumps(graph)

            # calculate clock matching information of all jumps
            pre_clk_m = self._calc_pre_clock_matching_info(graph)

            # gather the nodes that have the same pre- or post-states
            pre_equiv_dict = self._make_initial_equiv_class(graph, is_post=False)

            # calculate pre- and post-partition and merge them
            pre_equiv_rel = self._make_equiv_class(pre_equiv_dict, graph, pre_clk_m)

            # reduce graph using the partition
            self._reduce_pre_graph(graph, pre_equiv_rel)

            # calculate clock matching information for post equivalence
            post_clk_m = self._calc_post_clock_matching_info(graph)

            # gather the nodes that have the same pre- or post-states
            post_equiv_dict = self._make_initial_equiv_class(graph, is_post=True)

            # calculate pre- and post-partition and merge them
            post_equiv_rel = self._make_equiv_class(post_equiv_dict, graph, post_clk_m)

            # reduce graph using the partition
            self._reduce_post_graph(graph, post_equiv_rel)

            print("v: {}, e: {}".format(len(graph.get_nodes()), len(get_node_jumps(graph))))
            # break
            if old_v == graph.get_nodes() and old_e == get_node_jumps(graph):
                break

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

    def _make_equiv_class(self, equiv_dict: Dict[FrozenSet[Node], Set[Node]], graph: TableauGraph,
                          clock_matching: Dict[Node, ClockMatchingInfo]) -> List[Dict[Node, Set[Tuple[Node, ClockSubstitution]]]]:

        # make coarse equiv class regarding the label's propositions
        coarse_equiv_class = set()
        for num, eq_nodes in enumerate(equiv_dict):
            n_eq = self._make_coarse_equiv_class(equiv_dict[eq_nodes])
            coarse_equiv_class.update(n_eq)

        equiv_d_l = list()
        # check bisimulation relation to refine equivalent classes
        for c_eq_c in coarse_equiv_class:
            e_d = self._get_equiv_class(c_eq_c, clock_matching)
            tot = 0
            # assert that no states are missing
            for r_s in e_d:
                tot += 1 + len(e_d[r_s])
            assert tot == len(c_eq_c)
            equiv_d_l.append(e_d)

        return equiv_d_l
    @classmethod
    def _make_initial_equiv_class(cls, graph: TableauGraph, is_post=False) -> Dict[FrozenSet[Node], Set[Node]]:
        # get the nodes that have the same predecessors
        equiv_dict: Dict[FrozenSet[Node], Set[Node]] = dict()
        for node in graph.get_nodes():
            if node == graph.first_node():
                continue

            if is_post:
                equiv_class = frozenset(graph.get_next_vertices(node))
            else:
                equiv_class = frozenset(graph.get_pred_vertices(node))

            if equiv_class in equiv_dict:
                equiv_dict[equiv_class].add(node)
            else:
                equiv_dict[equiv_class] = {node}
        return equiv_dict

    def _make_coarse_equiv_class(self, nodes: Set[Node]) -> Set[FrozenSet[Node]]:
        equiv_dict: Dict[Tuple[FrozenSet[Proposition], bool, bool], Set[Node]] = dict()

        for node in nodes:
            nm = self._make_indexing_info(node)
            assert nm in self._node_indexing

            k = nm, node.is_initial(), node.is_final()
            if k in equiv_dict:
                equiv_dict[k].add(node)
            else:
                equiv_dict[k] = {node}

        equiv = set()
        for k in equiv_dict:
            equiv.add(frozenset(equiv_dict[k]))
        return equiv

    def _get_equiv_class(self, nodes: FrozenSet[Node],
                         clock_matching: Dict[Node, ClockMatchingInfo]) -> Dict[Node, Set[Tuple[Node, ClockSubstitution]]]:
        if len(nodes) <= 0:
            return dict()

        waiting_list = list(nodes)

        p_n = waiting_list.pop(0)
        equiv_d: Dict[Node, Set[Tuple[Node, ClockSubstitution]]] = {p_n: set()}

        while len(waiting_list) > 0:
            n = waiting_list.pop(0)
            found_equiv = False
            for node in equiv_d:
                # assert graph.get_next_vertices(node) == graph.get_next_vertices(n) for post-
                # assert graph.get_pred_vertices(node) == graph.get_pred_vertices(n) for pre-
                clk_subst = self._equiv_checking(node, n, clock_matching)

                if clk_subst is not None:
                    if node in equiv_d:
                        equiv_d[node].add((n, clk_subst))
                    else:
                        equiv_d[node] = {(n, clk_subst)}
                    found_equiv = True
                    break

            if not found_equiv:
                assert n not in equiv_d
                equiv_d[n] = set()

        return equiv_d

    # bisimulation ppst equivalence checking
    # return clock substitution when the nodes are bisimilar
    # otherwise return none
    def _equiv_checking(self, node1: Node, node2: Node,
                        clock_matching: Dict[Node, ClockMatchingInfo]) -> Optional[ClockSubstitution]:
        assert node1 in self._node_clocks and node2 in self._node_clocks

        c1_clk = self._node_clocks[node1]
        c2_clk = self._node_clocks[node2]

        # when the number of clocks are different,
        # the nodes are not bisimilar
        if len(c1_clk) != len(c2_clk):
            return None

        assert node1 in self._node_none_clk_goals and node2 in self._node_none_clk_goals

        # the non-timed goals (i.e., state propositions) must be the same
        non_clk_g1 = self._node_none_clk_goals[node1]
        non_clk_g2 = self._node_none_clk_goals[node2]
        if non_clk_g1 != non_clk_g2:
            return None

        assert node1 in clock_matching and node2 in clock_matching

        n1_cm = clock_matching[node1]
        n2_cm = clock_matching[node2]

        # check n1 -> n2
        clk_subst1 = n1_cm.match(n2_cm)

        # the two nodes cannot be the same
        if clk_subst1 is None:
            return None

        # check n2 -> n1
        clk_subst2 = n2_cm.match(n1_cm)

        if clk_subst2 is None:
            return None

        # choose one of the clock renaming
        return clk_subst1

    def _calc_post_clock_matching_info(self, graph: TableauGraph) -> Dict[Node, ClockMatchingInfo]:
        post_clock_matching: Dict[Node, ClockMatchingInfo] = dict()

        for node in graph.get_nodes():
            # ignore first dummy node
            if node == graph.first_node():
                continue

            assert node in self._node_aps
            # get aps and get information for post equivalence checking
            node_ap_s = self._node_aps[node]
            node_post_ap_s = set()
            for jp in graph.get_next_edges(node):
                for ap in jp.get_ap():
                    node_post_ap_s.add((ap, jp.get_trg()))

            for ap in node_ap_s:
                node_post_ap_s.add((ap, None))

            clk_m = ClockMatchingInfo()
            clk_m.add(*node_post_ap_s, is_post=True)

            assert node not in post_clock_matching
            post_clock_matching[node] = clk_m

        return post_clock_matching

    def _calc_pre_clock_matching_info(self, graph: TableauGraph) -> Dict[Node, ClockMatchingInfo]:
        pre_clock_matching: Dict[Node, ClockMatchingInfo] = dict()

        for node in graph.get_nodes():
            # ignore first dummy node
            if node == graph.first_node():
                continue

            assert node in self._node_aps
            # get aps and get information for post equivalence checking
            node_ap_s = self._node_aps[node]
            node_pre_ap_s = set()
            for jp in graph.get_pred_edges(node):
                for ap in jp.get_ap():
                    node_pre_ap_s.add((ap, jp.get_src()))

            for ap in node_ap_s:
                node_pre_ap_s.add((ap, None))

            clk_m = ClockMatchingInfo()
            clk_m.add(*node_pre_ap_s)

            assert node not in pre_clock_matching
            pre_clock_matching[node] = clk_m

        return pre_clock_matching


    def _calc_node_info(self, graph: TableauGraph):
        # ignore the first dummy node
        nodes = graph.get_nodes().copy()
        nodes.discard(graph.first_node())

        for node in nodes:
            assert node not in self._node_clock_goals
            assert node not in self._node_none_clk_goals
            assert node not in self._node_aps
            assert node not in self._node_clocks

            # calc node clock goals and non clock goals
            self._node_clock_goals[node] = filter_clock_goals(*node.cur_goals)
            self._node_none_clk_goals[node] = node.cur_goals.difference(self._node_clock_goals[node])

            # get aps
            node_ap_s = set(filter(lambda x: isinstance(x, Proposition), self._node_clock_goals[node]))
            node_ap_s.update(node.invariant)

            self._node_aps[node] = node_ap_s

            # get clocks
            self._node_clocks[node] = get_clock_pool(*node.cur_goals).union(get_clock_pool(*node.invariant))

            # calc node indexing
            indexing = self._make_indexing_info(node)
            if indexing in self._node_indexing:
                self._node_indexing[indexing].append(node)
            else:
                self._node_indexing[indexing] = [node]

    def _get_jump_clock_subst(self, jump1: Jump, jump2: Jump) -> Optional[ClockSubstitution]:
        assert jump1 in self._jump_clock_matching and jump2 in self._jump_clock_matching

        # get clock substitution
        jp1_m, jp2_m = self._jump_clock_matching[jump1], self._jump_clock_matching[jump2]
        return jp1_m.match(jp2_m)

    def _clear(self):
        self._jump_clock_matching.clear()
        self._node_indexing.clear()
        self._node_aps.clear()
        self._node_clocks.clear()
        self._node_clock_goals.clear()
        self._node_none_clk_goals.clear()

    @classmethod
    def _reduce_pre_graph(cls, graph: TableauGraph,
                          equiv_rel: List[Dict[Node, Set[Tuple[Node, ClockSubstitution]]]]):
        # refine graph
        for r_d in equiv_rel:
            for node in r_d:
                # remove vertex and copy its jumps
                for n, clk_subst in r_d[node]:
                    jp_p_s = graph.get_pred_edges(n)
                    jp_n_s = graph.get_next_edges(n)

                    # remove pred jumps
                    for jp in jp_p_s:
                        graph.remove_jump(jp)

                    # rewrite clocks at read positions
                    for jp in jp_n_s:
                        r_jp_ap = {clk_subst.substitute(f, is_write=False,
                                                        is_read=True) for f in jp.get_ap()}
                        new_jp = Jump(node, jp.get_trg(), r_jp_ap)
                        graph.add_jump(new_jp)

                    # remove equivalent node
                    graph.remove_node(n)

    @classmethod
    def _reduce_post_graph(cls, graph: TableauGraph,
                           equiv_rel: List[Dict[Node, Set[Tuple[Node, ClockSubstitution]]]]):
        # refine graph
        for r_d in equiv_rel:
            for node in r_d:
                # remove vertex and copy its jumps
                for n, clk_subst in r_d[node]:
                    jp_p_s = graph.get_pred_edges(n)
                    jp_n_s = graph.get_next_edges(n)

                    # rewrite clocks at write positions
                    for jp in jp_p_s:
                        r_jp_ap = {clk_subst.substitute(f, is_write=True,
                                                        is_read=False) for f in jp.get_ap()}
                        new_jp = Jump(jp.get_src(), node, r_jp_ap)
                        graph.add_jump(new_jp)

                    # remove next jumps
                    for jp in jp_n_s:
                        graph.remove_jump(jp)

                    # remove equivalent node
                    graph.remove_node(n)


def _fresh_group_id():
    counter = 0
    while True:
        yield counter
        counter += 1


class ClockMatchingInfo:
    def __init__(self):
        self._matching_info: Dict[Tuple[str, hash, hash], List[List[Real]]] = dict()

    def add(self, *goal_pairs, is_post=False):
        for f, n in goal_pairs:
            assert isinstance(f, Formula)
            assert isinstance(n, Node) or n is None
            self._add(f, n, is_post)

    def _add(self, goal: Formula, node: Optional[Node], is_post):
        info = _matching_info(goal, node, is_post)
        m_c = _get_matching_clock(goal, is_post)
        clk_s = [m_c] if m_c is not None else list()

        if info in self._matching_info:
            self._matching_info[info].append(clk_s)
        else:
            self._matching_info[info] = [clk_s]

    def match(self, other: 'ClockMatchingInfo') -> Optional[ClockSubstitution]:
        assert isinstance(other, ClockMatchingInfo)

        k_c = set(self._matching_info.keys())
        # information must be equal
        if k_c != set(other._matching_info.keys()):
            return None

        subst = clock_match(list(k_c), other._matching_info, self._matching_info, dict())
        if subst is None:
            return None

        clk_subst = ClockSubstitution()
        for k in subst:
            clk_subst.add(k, subst[k])

        return clk_subst

    def __repr__(self):
        m = "\n".join(["{} ---> {}".format(k, self._matching_info[k]) for k in self._matching_info])
        return "clock matching\n{}\n".format(m)


@singledispatch
def _matching_info(goal: Formula, node: Optional[Node], is_post: bool) -> Optional[Tuple[str, hash, hash]]:
    return None


@_matching_info.register(TimeProposition)
def _(goal: TimeProposition, node: Optional[Node], is_post: bool) -> Optional[Tuple[str, hash, hash]]:
    return "Time_{{{},{}}}".format(goal.temporal, goal.name_s), hash(goal.interval), hash(node)


@_matching_info.register(ClkAssn)
def _(goal: ClkAssn, node: Optional[Node], is_post: bool) -> Optional[Tuple[str, hash, hash]]:
    if is_post:
        return "assn", hash(goal.clock), hash(node)
    else:
        return "assn", hash(goal.value), hash(node)

@_matching_info.register(Close)
def _(goal: Close, node: Optional[Node], is_post: bool) -> Optional[Tuple[str, hash, hash]]:
    return "close", 0, hash(node)


@_matching_info.register(Open)
def _(goal: Open, node: Optional[Node], is_post: bool) -> Optional[Tuple[str, hash, hash]]:
    return "open", 0, hash(node)


@_matching_info.register(OpenClose)
def _(goal: OpenClose, node: Optional[Node], is_post: bool) -> Optional[Tuple[str, hash, hash]]:
    return "openClose", 0, hash(node)


@singledispatch
def _get_matching_clock(goal: Formula, is_post: bool) -> Optional[Real]:
    return None


@_get_matching_clock.register(ClkAssn)
def _(goal: ClkAssn, is_post: bool) -> Optional[Real]:
    if is_post:
        return None
    else:
        return goal.clock


@_get_matching_clock.register(OCProposition)
def _(goal: OCProposition, is_post: bool) -> Optional[Real]:
    return goal.get_clock()


@_get_matching_clock.register(TimeProposition)
def _(goal: TimeProposition, is_post: bool) -> Optional[Real]:
    return goal.clock