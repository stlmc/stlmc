from .graph import *
from .label import *

MatchKey = Tuple[str, hash, hash, str]
MatchVal = Optional[Real]
MatchInfo = Tuple[MatchKey, MatchVal]
MatchDict = Dict[MatchKey, Set[MatchVal]]


# pre and postfix equivalence
class PPEquivalence:
    def __init__(self):
        self._indexing: Dict[Node, Tuple[hash, hash]] = dict()
        self._node_indexing: Dict[Tuple[hash, hash], List[Node]] = dict()
        self._node_clocks: Dict[Node, Set[Real]] = dict()
        self._node_oc_time_prop: Dict[Node, Tuple[Set[Formula], Set[Formula]]] = dict()
        self.print_verbose = False
        self.print_debug = False

    def reduce(self, graph: TableauGraph):
        self._clear()

        self._calc_node_info(graph)

        loop = 0
        while True:
            loop += 1
            print("reduction iteration #{}".format(loop))
            old_v = graph.get_nodes().copy()
            old_e = get_node_jumps(graph)

            # calculate clock matching information of all jumps
            pre_clk_m = self._calc_clock_matching_info(graph)

            # gather the nodes that have the same pre- or post-states
            pre_equiv_dict = self._make_initial_equiv_class(graph, is_post=False)

            # calculate pre- and post-partition and merge them
            pre_equiv_rel = self._make_equiv_class(pre_equiv_dict, graph, pre_clk_m)

            # reduce graph using the partition
            self._reduce_pre_graph(graph, pre_equiv_rel)

            # calculate clock matching information for post equivalence
            post_clk_m = self._calc_clock_matching_info(graph, is_post=True)

            # gather the nodes that have the same pre- or post-states
            post_equiv_dict = self._make_initial_equiv_class(graph, is_post=True)

            # calculate pre- and post-partition and merge them
            post_equiv_rel = self._make_equiv_class(post_equiv_dict, graph, post_clk_m)

            # reduce graph using the partition
            self._reduce_post_graph(graph, post_equiv_rel)

            print("v: {}, e: {}".format(len(graph.get_nodes()), len(get_node_jumps(graph))))
            if old_v == graph.get_nodes() and old_e == get_node_jumps(graph):
                break

    def _make_indexing_info(self, node: 'Node') -> Tuple[hash, hash]:
        inv_idx = self._indexing_info(node.invariant)
        cur_idx = self._indexing_info(node.cur_goals)

        return hash(inv_idx), hash(cur_idx)

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
    def _oc_time_prop_info(cls, f_s: Set[Formula]) -> Set[Formula]:
        indexing = set()
        for f in f_s:
            if isinstance(f, OCProposition) or isinstance(f, TimeProposition):
                indexing.add(f)
        return indexing

    def _make_equiv_class(self, equiv_dict: Dict[FrozenSet[Node], Set[Node]], graph: TableauGraph,
                          clock_matching: Dict[Node, 'EquivClockMatching']) -> List[
        Dict[Node, Set[Tuple[Node, ClockSubstitution]]]]:

        # make coarse equiv class regarding the label's propositions
        coarse_equiv_class = set()
        for eq_nodes in equiv_dict:
            n_eq = self._make_coarse_equiv_class(equiv_dict[eq_nodes])
            coarse_equiv_class.update(n_eq)

        equiv_d_l, v_msg = list(), list()
        # check bisimulation relation to refine equivalent classes
        for c_eq_c in coarse_equiv_class:
            e_d = self._get_equiv_class(c_eq_c, clock_matching, graph)

            # msg
            if self.print_verbose:
                ss = ", ".join([str(len(e_d[n]) + 1) for n in e_d])
                v_msg.append((len(c_eq_c), ss))

            tot = 0
            # assert that no states are missing
            for r_s in e_d:
                tot += 1 + len(e_d[r_s])
            assert tot == len(c_eq_c)
            equiv_d_l.append(e_d)

        # msg
        if self.print_verbose:
            for g_id, (l, d) in enumerate(list(sorted(v_msg, key=lambda x: x[0]))):
                print("group#{} ({}) -- refined to --> ({})".format(g_id, l, d))
            print("----------")

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
        equiv_dict: Dict[Tuple[Tuple[hash, hash], bool, bool], Set[Node]] = dict()

        for node in nodes:
            assert node in self._indexing
            nm = self._indexing[node]

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

    def _get_equiv_class(self, nodes: FrozenSet[Node], clock_matching: Dict[Node, 'EquivClockMatching'],
                         graph: TableauGraph) -> Dict[Node, Set[Tuple[Node, ClockSubstitution]]]:
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
                clk_subst = self._equiv_checking(node, n, clock_matching, graph)
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

        # msg
        if self.print_debug:
            for e in equiv_d:
                print("to")
                print(e)
                print("@@@@@@@ -->")
                for n, clk in equiv_d[e]:
                    print(n)
                    print(clk)
            refined = ", ".join([str(len(equiv_d[e]) + 1) for e in equiv_d])
            print("=====({})===refined=to===>>({})==============".format(len(nodes), refined))

        return equiv_d

    # bisimulation pp equivalence checking
    # return clock substitution when the nodes are bisimilar
    # otherwise return none
    def _equiv_checking(self, node1: Node, node2: Node,
                        clock_matching: Dict[Node, 'EquivClockMatching'],
                        graph: TableauGraph) -> Optional[ClockSubstitution]:
        assert node1 in self._indexing and node2 in self._indexing
        assert node1 in self._node_clocks and node2 in self._node_clocks

        if len(self._node_clocks[node1]) != len(self._node_clocks[node2]):
            return None

        # the non-timed goals (i.e., state propositions) must be the same
        idx1, idx2 = self._indexing[node1], self._indexing[node2]
        if idx1 != idx2:
            return None

        assert node1 in clock_matching and node2 in clock_matching

        n1_cm = clock_matching[node1]
        n2_cm = clock_matching[node2]

        # check n1 -> n2
        clk_subst = n1_cm.match(n2_cm)

        # the two nodes cannot be the same
        if clk_subst is None:
            if self.print_debug:
                debug_msg = [
                    "cut by case ->",
                    "node1",
                    str(node1),
                    str(self._node_clocks[node1]),
                    "\n".join([str(jp) for jp in graph.get_pred_edges(node1)]),
                    "-------------",
                    "node2",
                    str(node2),
                    str(self._node_clocks[node2]),
                    "\n".join([str(jp) for jp in graph.get_pred_edges(node2)]),
                    "clk1 matching",
                    str(n1_cm),
                    "clk2 matching",
                    str(n2_cm),
                    "*****************"
                ]
                print("\n".join(debug_msg))

            return None

        if self.print_debug:
            debug_msg = [
                "found",
                str(clk_subst),
                "node1",
                str(node1),
                str(self._node_clocks[node1]),
                "\n".join([str(jp) for jp in graph.get_pred_edges(node1)]),
                "-------------",
                "node2",
                str(node2),
                str(self._node_clocks[node2]),
                "\n".join([str(jp) for jp in graph.get_pred_edges(node2)]),
                "clk1 matching",
                str(n1_cm),
                "clk2 matching",
                str(n2_cm),
                "*****************"
            ]
            print("\n".join(debug_msg))

        return clk_subst

    def _calc_clock_matching_info(self, graph: TableauGraph, is_post=False) -> Dict[Node, 'EquivClockMatching']:
        clock_matching: Dict[Node, EquivClockMatching] = dict()
        # handle read positions when pre-equiv.
        is_read = not is_post

        for node in graph.get_nodes():
            # ignore first dummy node
            if node == graph.first_node():
                continue

            assert node in self._node_clocks
            clk_m = EquivClockMatching(self._node_clocks[node])

            if is_post:
                jp_s = graph.get_next_edges(node)
            else:
                jp_s = graph.get_pred_edges(node)

            # get aps and get information for pre equivalence checking
            for jp in jp_s:
                for ap in jp.get_ap():
                    if is_post:
                        n = jp.get_trg(),
                    else:
                        n = jp.get_src()

                    clk_m.add(ap, "jp", n, is_read)

            assert node in self._node_oc_time_prop
            inv, cur = self._node_oc_time_prop[node]
            for f in inv:
                clk_m.add(f, "inv", None, is_read)

            for g in cur:
                clk_m.add(g, "cur", None, is_read)

            assert node not in clock_matching
            clock_matching[node] = clk_m

        return clock_matching

    def _calc_node_info(self, graph: TableauGraph):
        for node in graph.get_nodes():
            # ignore the first dummy node
            if node == graph.first_node():
                continue

            # calc node indexing
            indexing = self._make_indexing_info(node)
            if indexing in self._node_indexing:
                self._node_indexing[indexing].append(node)
            else:
                self._node_indexing[indexing] = [node]

            assert node not in self._indexing
            self._indexing[node] = indexing

            # calc oc time proposition
            assert node not in self._node_oc_time_prop

            inv, cur = self._oc_time_prop_info(node.invariant), self._oc_time_prop_info(node.cur_goals)
            self._node_oc_time_prop[node] = (inv, cur)

            assert node not in self._node_clocks
            self._node_clocks[node] = get_clock_pool(*node.invariant).union(get_clock_pool(*node.cur_goals))

    def _clear(self):
        self._indexing.clear()
        self._node_indexing.clear()
        self._node_clocks.clear()
        self._node_oc_time_prop.clear()

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


class EquivClockMatching:
    def __init__(self, clocks: Set[Real]):
        self._matching_info: MatchDict = dict()
        self._clocks = clocks.copy()

    def add(self, goal: Formula, ty: str, node: Optional[Node], is_read: bool):
        k, v = _matching_info(goal, ty, node, is_read)

        if k in self._matching_info:
            self._matching_info[k].add(v)
        else:
            self._matching_info[k] = {v}

    def match(self, other: 'EquivClockMatching') -> Optional[ClockSubstitution]:
        assert isinstance(other, EquivClockMatching)

        if len(self._clocks) != len(other._clocks):
            return None

        k_c = set(self._matching_info.keys())
        # information must be equal
        if k_c != set(other._matching_info.keys()):
            return None

        subst = equiv_clock_match(self._matching_info, other._matching_info, list(k_c), 0, dict())
        if subst is None:
            return None

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


@singledispatch
def _matching_info(goal: Formula, ty: str, node: Optional[Node], is_read: bool) -> Optional[MatchInfo]:
    return None


@_matching_info.register(TimeProposition)
def _(goal: TimeProposition, ty: str, node: Optional[Node], is_read: bool) -> Optional[MatchInfo]:
    n = "T_{{{},{}}}".format(goal.temporal, goal.name_s)
    h1, h2 = hash(goal.interval), hash(node)
    if is_read:
        return (n, h1, h2, ty), goal.clock
    else:
        ty = "{}@{}".format(ty, hash(goal.clock))
        return (n, h1, h2, ty), None


@_matching_info.register(TimeBound)
def _(goal: TimeBound, ty: str, node: Optional[Node], is_read: bool) -> Optional[MatchInfo]:
    return ("tb", 0, hash(node), ty), None


@_matching_info.register(TimeFinal)
def _(goal: TimeFinal, ty: str, node: Optional[Node], is_read: bool) -> Optional[MatchInfo]:
    return (str(goal), 0, hash(node), ty), None


@_matching_info.register(ClkAssn)
def _(goal: ClkAssn, ty: str, node: Optional[Node], is_read: bool) -> Optional[MatchInfo]:
    if is_read:
        if isinstance(goal.value, Real):
            return ("assn", hash(goal.clock), hash(node), ty), goal.value
        else:
            return ("assn", hash(goal.clock), hash(node), "{}@{}".format(ty, hash(goal.value))), None
    else:
        return ("assn", hash(goal.value), hash(node), ty), goal.clock


@_matching_info.register(Close)
def _(goal: Close, ty: str, node: Optional[Node],
      is_read: bool) -> Optional[MatchInfo]:
    if is_read:
        return ("close", 0, hash(node), ty), goal.get_clock()
    else:
        return ("close", hash(goal.get_clock()), hash(node), ty), None


@_matching_info.register(Open)
def _(goal: Open, ty: str, node: Optional[Node],
      is_read: bool) -> Optional[MatchInfo]:
    if is_read:
        return ("open", 0, hash(node), ty), goal.get_clock()
    else:
        return ("open", hash(goal.get_clock()), hash(node), ty), None


@_matching_info.register(OpenClose)
def _(goal: OpenClose, ty: str, node: Optional[Node],
      is_read: bool) -> Optional[MatchInfo]:
    if is_read:
        return ("openClose", 0, hash(node), ty), goal.get_clock()
    else:
        return ("openClose", hash(goal.get_clock()), hash(node), ty), None


# find clock renaming that renames match1 equivalent to match2
# \theta(match1) = match2
def equiv_clock_match(match1: MatchDict, match2: MatchDict,
                      positions: List[MatchKey], index: int,
                      subst: Dict[Real, Real]) -> Optional[Dict[Real, Real]]:
    # if no element left
    if len(positions) <= index:
        return subst

    pos = positions[index]
    m_clk1_s, m_clk2_s = match1[pos], match2[pos]

    if len(m_clk1_s) != len(m_clk2_s):
        return None

    # fixed ordering of clocks in match1
    t_clk1 = tuple(m_clk1_s)
    t_clk2_list = list(permutations(m_clk2_s))

    for t_clk2 in t_clk2_list:
        assert isinstance(t_clk2, Tuple)

        n_subst = _match_clk(t_clk1, t_clk2, subst)
        if n_subst is None:
            continue

        m = equiv_clock_match(match1, match2, positions, index + 1, n_subst)
        if m is not None:
            return m

    return None


# rename e1 --> e2
def _match_clk(e1: Tuple[MatchVal], e2: Tuple[MatchVal], subst: Dict[Real, Real]) -> Optional[Dict[Real, Real]]:
    assert len(e1) == len(e2)

    new_subst = subst.copy()

    for clk1, clk2 in list(zip(e1, e2)):
        if (clk1 is None) != (clk2 is None):
            return None

        if clk1 is None and clk2 is None:
            continue

        assert isinstance(clk1, Real) and isinstance(clk2, Real)

        if clk1 in new_subst:
            # conflict
            if not variable_equal(new_subst[clk1], clk2):
                return None
        else:
            new_subst[clk1] = clk2

    return new_subst
