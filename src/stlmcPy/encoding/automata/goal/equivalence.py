from .graph import *
from .label import *


# pre and postfix equivalence
class PPEquivalence:
    def __init__(self):
        self._jump_clock_matching: Dict[Jump, ClockMatchingInfo] = dict()
        self._node_indexing: Dict[FrozenSet[Proposition], List[Node]] = dict()

    def reduce(self, graph: TableauGraph):
        self._clear()
        # ignore the first dummy node
        nodes = graph.get_nodes().copy()
        nodes.discard(graph.first_node())

        # make node indexing
        for node in nodes:
            indexing = self._make_indexing_info(node)
            if indexing in self._node_indexing:
                self._node_indexing[indexing].append(node)
            else:
                self._node_indexing[indexing] = [node]

        iter = 0
        while True:
            iter += 1
            print("reduction iteration #{}".format(iter))
            old_v = graph.get_nodes().copy()
            old_e = get_node_jumps(graph)

            # calculate clock matching information of all jumps
            self._calc_jump_clock_matching_info(graph)

            # calculate pre- and post-partition and merge them
            pre_equiv_rel = self._make_equiv_class(graph)

            # reduce graph using the partition
            self._reduce_pre_graph(graph, pre_equiv_rel)

            # calculate clock matching information of all jumps
            self._calc_jump_clock_matching_info(graph, is_post=True)

            # calculate pre- and post-partition and merge them
            post_equiv_rel = self._make_equiv_class(graph, is_post=True)

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

    def _make_equiv_class(self, graph: TableauGraph,
                          is_post=False) -> List[Dict[Node, Set[Tuple[Node, ClockSubstitution]]]]:
        # gather the nodes that have the same pre- or post-states
        equiv_dict = self._make_initial_equiv_class(graph, is_post)

        # make coarse equiv class regarding the label's propositions
        coarse_equiv_class = set()
        for num, eq_nodes in enumerate(equiv_dict):
            n_eq = self._make_coarse_equiv_class(equiv_dict[eq_nodes])
            coarse_equiv_class.update(n_eq)

        equiv_d_l = list()
        # check bisimulation relation to refine equivalent classes
        for c_eq_c in coarse_equiv_class:
            e_d = self._get_equiv_class(c_eq_c, graph, is_post)
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
                         graph: TableauGraph, is_post=False) -> Dict[Node, Set[Tuple[Node, ClockSubstitution]]]:
        if len(nodes) <= 0:
            return dict()

        waiting_list = list(nodes)

        p_n = waiting_list.pop(0)
        equiv_d: Dict[Node, Set[Tuple[Node, ClockSubstitution]]] = {p_n: set()}

        while len(waiting_list) > 0:
            n = waiting_list.pop(0)
            found_equiv = False
            for node in equiv_d:
                reason = set()
                if is_post:
                    clk_subst = self._post_checking(node, n, graph, reason)
                else:
                    clk_subst = self._pre_checking(node, n, graph)

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

    # bisimulation pre equivalence checking
    # return clock substitution when the nodes are bisimilar
    # otherwise return none
    def _pre_checking(self, node1: Node, node2: Node, graph: TableauGraph) -> Optional[ClockSubstitution]:
        pred_s = graph.get_pred_vertices(node1)
        assert pred_s == graph.get_pred_vertices(node2)

        # get pre edges
        node1_jp_pre = graph.get_pred_edges(node1)
        node2_jp_pre = graph.get_pred_edges(node2)

        c1_clk = get_clock_pool(*node1.cur_goals)
        c2_clk = get_clock_pool(*node2.cur_goals)

        # when the number of clocks are different,
        # the nodes are not bisimilar
        if len(c1_clk) != len(c2_clk):
            return None

        # the non-timed goals (i.e., state propositions) must be the same
        non_clk_g1 = node1.cur_goals.difference(filter_clock_goals(*node1.cur_goals))
        non_clk_g2 = node2.cur_goals.difference(filter_clock_goals(*node2.cur_goals))

        if non_clk_g1 != non_clk_g2:
            return None

        clk_subst, forbidden = None, set()

        for node in pred_s:
            n_jp = graph.get_next_edges(node)
            n1_jp = n_jp.intersection(node1_jp_pre)
            n2_jp = n_jp.intersection(node2_jp_pre)

            clk_subst, forbidden = self._find_pre_clk_subst(n1_jp, n2_jp, clk_subst, forbidden, graph, True)

            # the two nodes cannot be the same
            if clk_subst is None:
                return None


            clk_subst, forbidden = self._find_pre_clk_subst(n2_jp, n1_jp, clk_subst, forbidden, graph, False)

            if clk_subst is None:
                return None

        return clk_subst

    def _find_pre_clk_subst(self, node1_jp_pre: Set[Jump], node2_jp_pre: Set[Jump],
                        clk_subst: Optional[ClockSubstitution],
                        forbidden: Set[ClockSubstitution],
                        graph: TableauGraph, right2left: bool) -> Tuple[Optional[ClockSubstitution], Set[ClockSubstitution]]:
        # if right2left is true, rewrite jumps in node2_jp_pre using clk_subst
        # and see if they can be same as the jumps in the node1_jp_pre
        fb = forbidden.copy()
        if len(node1_jp_pre) <= 0:
            return clk_subst, fb

        n1_jp_pre = node1_jp_pre.copy()
        n2_jp_pre = node2_jp_pre.copy()
        jp1 = n1_jp_pre.pop()
        for jp2 in node2_jp_pre:
            if len(jp1.get_ap()) != len(jp2.get_ap()):
                continue

            # try to get a clock renaming if none is given
            if clk_subst is None:
                n_clk_subst = self._get_jump_clock_subst(jp1, jp2, fb)
            else:
                n_clk_subst = clk_subst

            # if still cannot find a substitution
            # the two jumps cannot be the same
            if n_clk_subst is None:
                continue

            if right2left:
                jp1_ap = jp1.get_ap()
                jp2_ap = {n_clk_subst.substitute(ap, is_write=True, is_read=False) for ap in jp2.get_ap()}
            else:
                jp1_ap = {n_clk_subst.substitute(ap, is_write=True, is_read=False) for ap in jp1.get_ap()}
                jp2_ap = jp2.get_ap()

            # found equivalent jp2
            if jp1_ap == jp2_ap:
                f_clk, f_s = self._find_pre_clk_subst(n1_jp_pre, n2_jp_pre, n_clk_subst, fb, graph, right2left)
                return f_clk, f_s

            fb.add(n_clk_subst)

        return None, fb


    # bisimulation ppst equivalence checking
    # return clock substitution when the nodes are bisimilar
    # otherwise return none
    def _post_checking(self, node1: Node, node2: Node, graph: TableauGraph, reason: Set[Tuple[FrozenSet[Jump],
    FrozenSet[Jump], str]]) -> Optional[ClockSubstitution]:
        next_s = graph.get_next_vertices(node1)
        assert next_s == graph.get_next_vertices(node2)

        # get pre edges
        node1_jp_post = graph.get_next_edges(node1)
        node2_jp_post = graph.get_next_edges(node2)

        c1_clk = get_clock_pool(*node1.cur_goals)
        c2_clk = get_clock_pool(*node2.cur_goals)

        # when the number of clocks are different,
        # the nodes are not bisimilar
        if len(c1_clk) != len(c2_clk):
            return None

        # the non-timed goals (i.e., state propositions) must be the same
        non_clk_g1 = node1.cur_goals.difference(filter_clock_goals(*node1.cur_goals))
        non_clk_g2 = node2.cur_goals.difference(filter_clock_goals(*node2.cur_goals))

        if non_clk_g1 != non_clk_g2:
            return None

        clk_subst, forbidden = None, set()

        for node in next_s:
            n_jp = graph.get_pred_edges(node)
            n1_jp = n_jp.intersection(node1_jp_post)
            n2_jp = n_jp.intersection(node2_jp_post)

            clk_subst, forbidden = self._find_post_clk_subst(n1_jp, n2_jp, clk_subst, forbidden, graph, True)

            # the two nodes cannot be the same
            if clk_subst is None:
                reason.add((frozenset(n1_jp), frozenset(n2_jp), "failed ->"))
                return None

            clk_subst, forbidden = self._find_post_clk_subst(n2_jp, n1_jp, clk_subst, forbidden, graph, False)

            if clk_subst is None:
                reason.add((frozenset(n2_jp), frozenset(n1_jp), "failed <-"))
                return None

        inv = {clk_subst.substitute(f, is_write=False, is_read=True) for f in node2.invariant}
        if inv != node1.invariant:
            return None

        return clk_subst

    def _find_post_clk_subst(self, node1_jp_post: Set[Jump], node2_jp_post: Set[Jump],
                             clk_subst: Optional[ClockSubstitution],
                             forbidden: Set[ClockSubstitution],
                             graph: TableauGraph, right2left: bool) -> Tuple[Optional[ClockSubstitution], Set[ClockSubstitution]]:
        fb = forbidden.copy()
        if len(node1_jp_post) <= 0:
            return clk_subst, fb

        n1_jp_post = node1_jp_post.copy()
        n2_jp_post = node2_jp_post.copy()
        jp1 = n1_jp_post.pop()
        for jp2 in node2_jp_post:
            if len(jp1.get_ap()) != len(jp2.get_ap()):
                continue

            # try to get a clock renaming if none is given
            if clk_subst is None:
                n_clk_subst = self._get_jump_clock_subst(jp1, jp2, fb)
            else:
                n_clk_subst = clk_subst

            # if still cannot find a substitution
            # the two jumps cannot be the same
            if n_clk_subst is None:
                continue

            if right2left:
                jp1_ap = set(jp1.get_ap())
                jp2_ap = {n_clk_subst.substitute(ap, is_write=False, is_read=True) for ap in jp2.get_ap()}
            else:
                jp1_ap = {n_clk_subst.substitute(ap, is_write=False, is_read=True) for ap in jp1.get_ap()}
                jp2_ap = set(jp2.get_ap())

            # found equivalent jp2
            if jp1_ap == jp2_ap:
                f_clk, f_s = self._find_post_clk_subst(n1_jp_post, n2_jp_post, n_clk_subst, fb, graph, right2left)
                return f_clk, f_s

            fb.add(n_clk_subst)
            return self._find_post_clk_subst(node1_jp_post, node2_jp_post, None, fb, graph, right2left)

        return None, fb

    def _calc_jump_clock_matching_info(self, graph: TableauGraph, is_post=False):
        # clear previous jumps' clock matching
        self._jump_clock_matching.clear()

        jp_s = get_node_jumps(graph)
        for jp in jp_s:
            assert jp not in self._jump_clock_matching
            clk_m = ClockMatchingInfo()
            c_s = set(jp.get_ap())

            # need to consider invariants
            if is_post:
                clk_m.add(*c_s.union(jp.get_src().invariant))
            else:
                clk_m.add(*c_s.union(jp.get_trg().invariant))

            self._jump_clock_matching[jp] = clk_m

    def _get_jump_clock_subst(self, jump1: Jump, jump2: Jump,
                              forbidden: Set[ClockSubstitution]) -> Optional[ClockSubstitution]:
        assert jump1 in self._jump_clock_matching and jump2 in self._jump_clock_matching

        fb_list = list()
        for clk_subst in forbidden:
            fb_list.append(clk_subst.dict())

        # get clock substitution
        jp1_m, jp2_m = self._jump_clock_matching[jump1], self._jump_clock_matching[jump2]
        return jp1_m.match(jp2_m, fb_list)

    def _clear(self):
        self._jump_clock_matching.clear()
        self._node_indexing.clear()

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
        self._other: Set[Formula] = set()

    def add(self, *goals):
        for f in goals:
            assert isinstance(f, Formula)
            self._add(f)

    def _add(self, goal: Formula):
        info = _matching_info(goal)

        if info is None:
            self._other.add(goal)
            return

        if info in self._matching_info:
            self._matching_info[info].append([_get_matching_clock(goal)])
        else:
            self._matching_info[info] = [[_get_matching_clock(goal)]]

    def match(self, other: 'ClockMatchingInfo',
              forbidden: List[Dict[Real, Real]]) -> Optional[ClockSubstitution]:
        assert isinstance(other, ClockMatchingInfo)

        if len(self._other) != len(other._other):
            return None

        if self._other != other._other:
            return None

        k_c = set(self._matching_info.keys())
        # information must be equal
        if k_c != set(other._matching_info.keys()):
            return None

        subst = clock_match(list(k_c), other._matching_info, self._matching_info, dict(), forbidden)
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
def _matching_info(goal: Formula) -> Optional[Tuple[str, hash, hash]]:
    return None


@_matching_info.register(TimeProposition)
def _(goal: TimeProposition) -> Optional[Tuple[str, hash, hash]]:
    return "Time_{{{},{}}}".format(goal.temporal, goal.name_s), hash(goal.interval), 0


@_matching_info.register(ClkAssn)
def _(goal: ClkAssn) -> Optional[Tuple[str, hash, hash]]:
    return "assn", hash(goal.value), 0

@_matching_info.register(Close)
def _(goal: Close) -> Optional[Tuple[str, hash, hash]]:
    return "close", 0, 0


@_matching_info.register(Open)
def _(goal: Open) -> Optional[Tuple[str, hash, hash]]:
    return "open", 0, 0


@_matching_info.register(OpenClose)
def _(goal: OpenClose) -> Optional[Tuple[str, hash, hash]]:
    return "openClose", 0, 0


@singledispatch
def _get_matching_clock(goal: Formula) -> Optional[Real]:
    return None


@_get_matching_clock.register(ClkAssn)
def _(goal: ClkAssn) -> Optional[Real]:
    return goal.clock


@_get_matching_clock.register(OCProposition)
def _(goal: OCProposition) -> Optional[Real]:
    return goal.get_clock()


@_get_matching_clock.register(TimeProposition)
def _(goal: TimeProposition) -> Optional[Real]:
    return goal.clock