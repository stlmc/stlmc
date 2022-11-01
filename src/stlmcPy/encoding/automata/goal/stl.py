import time

from .aux import *
from .clock import global_clk_subst
from .equivalence import ShiftingEquivalenceChecker, StutteringEquivalenceChecker
from .graph import *
from .ha_converter import HAConverter, shift_reset
from .optimizer import ContradictionChecker
from .subsumption import ForwardSubsumption, BackwardSubsumption, PathSubsumption
from ...smt.goal.aux import *
from ....constraints.aux.operations import *
from ....hybrid_automaton.hybrid_automaton import *
from ....objects.goal import Goal
from .label import *


class StlGoal(Goal):
    def __init__(self, formula: Formula, config: Dict):
        super().__init__(formula)

        # check configuration
        assert "threshold" in config and "prop_dict" in config
        assert "time-bound" in config and "bound" in config

        # type checking
        assert isinstance(config["threshold"], float)
        assert isinstance(config["time-bound"], float)
        assert isinstance(config["bound"], int)
        assert isinstance(config["prop_dict"], Dict)

        self.threshold = config["threshold"]
        self.prop_dict = config["prop_dict"]
        self.tau_max = config["time-bound"]
        self.bound = config["bound"]

        # build substitution for user-defined propositions
        subst = Substitution()
        for p in self.prop_dict:
            subst.add(p, self.prop_dict[p])

        self.tau_subst = VarSubstitution()
        self.tau_subst.add(tau_max(), RealVal(str(self.tau_max)))
        self.clk_subst_dict = global_clk_subst(int(self.bound))

        # get an eps-strengthening reduced formula
        self._formula = strengthen_reduction(subst.substitute(self.formula), self.threshold)

        #
        self._optimizer = ContradictionChecker(self.clk_subst_dict, self.tau_subst)
        self._label_generator = LabelGenerator(self._formula, threshold=self.threshold)
        self._stuttering_checker = StutteringEquivalenceChecker(self._formula)
        self._shifting_checker = ShiftingEquivalenceChecker(self._formula)
        self._graph_generator = GraphGenerator(self._formula, self._optimizer, self._shifting_checker, shift_mode=True)
        self._hybrid_converter = HAConverter(self.tau_subst)

        self._forward_subsumption = ForwardSubsumption()
        self._backward_subsumption = BackwardSubsumption()
        self._path_subsumption = PathSubsumption(self._forward_subsumption.get_relation(),
                                                 self._backward_subsumption.get_relation())

    def encode(self):
        self._graph_generator.clear()
        self._hybrid_converter.clear()
        graph = self._graph_generator.graph
        converter = self._hybrid_converter
        lg = self._label_generator
        st_checker = self._stuttering_checker
        bound = self.bound

        alg_s_t = time.time()
        init_labels = lg.init()
        init_labels = set(filter(lambda x: not self._optimizer.check_contradiction(x, 1, *_time_ordering(graph.get_max_depth())), init_labels))

        # make initial nodes
        for label in init_labels:
            self._graph_generator.make_node(label)
        self._graph_generator.finish_depth()

        wait_queue: Set[Label] = init_labels
        next_queue: Set[Label] = set()

        total_label = len(init_labels)
        total_nodes = len(graph.get_nodes_at(1))
        depth, final_depth = 2, bound
        while True:
            if depth > final_depth:
                break

            s = time.time()
            # print("depth : {}".format(depth))
            for label in wait_queue:
                # check
                # print("  label: {}".format(label))
                if self._optimizer.check_contradiction(label, depth):
                    continue

                n = lg.expand(label, depth)
                n = set(filter(lambda x: not self._optimizer.check_contradiction(x, depth, *_time_ordering(graph.get_max_depth())), n))
                # n = self._apply_reduction(n)
                n = st_checker.stuttering(label, n)

                next_queue.update(n)
                # next_queue = canonicalize(next_queue)
                # print_extend(label, n)

                if final_depth >= depth:
                    self._graph_generator.make_posts(label, n)

            e = time.time()
            wait_queue = next_queue.copy()
            # wait_queue = self._apply_reduction(next_queue)
            next_queue.clear()

            #
            if depth <= graph.get_max_depth():
                cur_nodes = len(graph.get_nodes_at(depth))
            else:
                cur_nodes = 0

            num_labels = len(wait_queue)
            total_label += num_labels
            total_nodes += cur_nodes

            print("depth#{}, labels#{}, labelsAcc#{}, nodes#{}, nodesAcc#{}".format(depth,
                                                                                    num_labels,
                                                                                    total_label,
                                                                                    cur_nodes,
                                                                                    total_nodes))
            logging = ["translate: {:.3f}".format(self._optimizer.translate_time),
                       "contradiction: {:.3f}".format(self._optimizer.contradiction_time),
                       "contradiction call# {}".format(self._optimizer.contradiction_call),
                       "solver time: {:.3f}".format(self._optimizer.z3obj_time),
                       "total: {:.3f}".format(e - s)]

            print("{}".format("\n".join(map(lambda x: indented_str(x, 2), logging))))
            self._optimizer.time_clear()
            self._graph_generator.finish_depth()
            depth += 1

        self._graph_generator.remove_contradiction()
        self._graph_generator.make_shift_resets()
        self._graph_generator.remove_redundancy()
        alg_e_t = time.time()
        print("running time: {:.3f}s".format(alg_e_t - alg_s_t))

        print("after remove unreachable")
        s_t = time.time()
        self._graph_generator.remove_unreachable()
        e_t = time.time()
        print("unreach remove : {:.3f}s".format(e_t - s_t))
        print_graph_info(graph)

        self._forward_subsumption.calc_relation(graph)
        self._forward_subsumption.reduce(graph)
        print()
        print("forward subsumption")
        print_graph_info(graph)

        self._backward_subsumption.calc_relation(graph)
        self._backward_subsumption.reduce(graph)
        print()
        print("backward subsumption")
        print_graph_info(graph)

        self._path_subsumption.reduce(graph)
        print()
        print("subsumption")
        print_graph_info(graph)

        ha = converter.convert(graph, self._graph_generator._resets)
        # import pickle
        # with open("{}.graph".format("stl"), "wb") as fw:
        #     pickle.dump(graph, fw)
        # with open("{}.automata".format("stl"), "wb") as fw:
        #     pickle.dump(ha, fw)
        return ha


class GraphGenerator:
    def __init__(self, top_formula: Formula, contradiction_checker: ContradictionChecker,
                 shifting_checker: ShiftingEquivalenceChecker, shift_mode=False):
        self.graph = TableauGraph()
        self._resets: Dict[Jump, Tuple[int, int]] = dict()
        self._shifting_checker = shifting_checker
        self._formula = top_formula
        self._contradiction_checker = contradiction_checker

        # graph info
        self._node_id_dict: Dict[Tuple[FrozenSet[Formula], int], Node] = dict()
        self.shifting_mode = shift_mode

        # current depth of the graph
        # current generation depth should be _cur_max_graph_depth + 1
        self._cur_max_graph_depth = 1

    def clear(self):
        self.graph = TableauGraph()
        self._resets = dict()
        self._node_id_dict = dict()
        self._cur_max_graph_depth = 1

    def finish_depth(self):
        self._cur_max_graph_depth = self.graph.get_max_depth() + 1

    def make_posts(self, parent_label: Label, post_labels: Set[Label]):
        depth = self._get_graph_depth() + 1

        post_nodes = set()
        for post in post_labels:
            # do not make node for empty label
            assert not is_empty_labels(post)
            post_nodes.add(self._shift_eq_node(post))

        # if parent exists
        is_p_found, p_depth = self._find_node_by_lb(parent_label, find_prev=True)
        if is_p_found:
            p_lb = self._cur_formulas(parent_label)
            parent = self._node_id_dict[(p_lb, p_depth)]

            for is_shift_node, node in post_nodes:
                jp = Jump(parent, node)
                connect(jp)

                if is_shift_node:
                    shift = self._shifting_checker.get_shifting()
                    assert jp not in self._resets
                    self._resets[jp] = (p_depth + 1, shift)
        else:
            raise Exception("labels should have a parent")

    def make_node(self, label: Label):
        lb = self._cur_formulas(label)
        depth = self._get_graph_depth()

        # do not make node for empty label
        if is_empty_labels(label):
            raise Exception("label cannot be empty")

        # if node already exists
        is_found, lb_depth = self._find_node_by_lb(label)
        if is_found:
            return self._node_id_dict[(lb, lb_depth)]

        node = Node(hash((label, depth)), depth)
        node.non_intermediate, node.intermediate = split_label(label)

        self.graph.add_node(node)
        self._node_id_dict[(lb, depth)] = node

        if _is_final_label(label):
            node.set_as_final()

        if _is_initial_node(node):
            node.set_as_initial()

        return node

    def remove_unreachable(self):
        reach = _find_reachable(self.graph)

        remove = set()
        for d in range(self.graph.get_max_depth()):
            nodes = self.graph.get_nodes_at(d + 1)
            for node in nodes:
                if node not in reach:
                    remove.add(node)

        for node in remove:
            self.graph.remove_node(node)

    def remove_redundancy(self):
        jp_s = get_node_jumps(self.graph)
        jp_dict: Dict[Tuple[Node, Node, FrozenSet[Tuple[Real, Formula]]], Set[Jump]] = dict()

        for jp in jp_s:
            k = jp.src, jp.trg, frozenset(jp.reset)
            if k in jp_dict:
                jp_dict[k].add(jp)
            else:
                jp_dict[k] = {jp}

        # remove redundant jumps
        for k in jp_dict:
            # pop representative jump
            jp_dict[k].pop()
            for jp in jp_dict[k]:
                self.graph.remove_jump(jp)

    def remove_contradiction(self):
        to_be_removed = set()
        for node in self.graph.nodes:
            lb = Label(singleton(*node.non_intermediate), singleton(),
                       singleton(), singleton())
            if self._contradiction_checker.check_contradiction(lb, node.depth):
                to_be_removed.add(node)

        for node in to_be_removed:
            self.graph.remove_node(node)

    def make_shift_resets(self):
        max_depth = self.graph.get_max_depth()
        for jp in self._resets:
            depth, shift = self._resets[jp]
            jp.add_reset(*shift_reset(depth, shift, max_depth))

    def _find_node_by_lb(self, label: Label, find_prev=False) -> Tuple[bool, int]:
        c_lb = self._cur_formulas(label)
        depth = self._get_graph_depth(find_prev)

        if self.shifting_mode:
            for lb, d in self._node_id_dict:
                if d > depth:
                    continue
                if lb == c_lb:
                    return True, d
        else:
            if (c_lb, depth) in self._node_id_dict:
                return True, depth
        return False, -1

    def _shift_eq_node(self, label: Label) -> Tuple[bool, Node]:
        lb = self._cur_formulas(label)
        depth = self._get_graph_depth()

        if self.shifting_mode:
            # get nodes less than current depth and find
            prev_nodes = set(filter(lambda n: n.depth < depth, self.graph.nodes))

            for node in prev_nodes:
                # infer label
                node_lb = Label(singleton(*node.non_intermediate.union(node.intermediate)),
                                singleton(), singleton(), singleton())
                # get depths
                depth1, depth2 = node.depth, depth

                # return if any found
                if self._shifting_checker.equivalent(node_lb, label, is_full=True,
                                                     depth1=depth1, depth2=depth2):
                    self._node_id_dict[(lb, depth1)] = node
                    return True, node

                # return if any found
                if self._shifting_checker.equivalent(node_lb, label, is_full=False,
                                                     depth1=depth1, depth2=depth2,):
                    self._node_id_dict[(lb, depth1)] = node
                    return True, node

        # make a new node
        return False, self.make_node(label)

    def _cur_formulas(self, label: Label):
        return frozenset(label.cur.difference({self._formula}))

    def _get_graph_depth(self, find_prev=False):
        # get current generation depth
        if find_prev:
            return self._cur_max_graph_depth - 1
        else:
            return self._cur_max_graph_depth


def is_empty_labels(label: Label):
    return len(label.cur) == 0


def _find_reachable(graph: TableauGraph) -> Set[Node]:
    # set finals as reachable nodes
    reach, un_reach = set(filter(lambda n: n.is_final(), graph.nodes)), set()

    # prepare rest of the nodes
    waiting = graph.nodes.difference(reach)
    while len(waiting) > 0:
        for node in waiting:
            n_succ = node.get_out_vertices()
            # else at least one successor is reachable
            if len(n_succ.intersection(reach)) > 0:
                reach.add(node)

            # all successors are unreachable
            if n_succ.issubset(un_reach):
                un_reach.add(node)

        waiting.difference_update(reach)
        waiting.difference_update(un_reach)

    return reach


def _is_final_label(label: Label):
    return len(label.nxt) == 0


def _is_initial_node(node: Node):
    return node.depth == 1


def print_wait_queue(wait_queue: Set[Label]):
    print()
    print("lb wait queue >")
    for p_l in wait_queue:
        print(indented_str(str(p_l), 2))


def print_graph_info(graph: TableauGraph):
    print("graph size #{}".format(len(graph.nodes)))
    for d in range(graph.get_max_depth()):
        print("depth@{} --> graph node#{}".format(d + 1, len(graph.get_nodes_at(d + 1))))
        # for index, node in enumerate(graph.get_nodes_at(d + 1)):
        #     print(indented_str("node{} --> pred: {}, succ: {}".format(index, len(node.pred), len(node.succ)), 2))


def print_extend(label: Label, labels_set: Set[Label]):
    print("extend label")
    print(indented_str(str(label), 2))
    print()
    print(indented_str("------>", 2))
    print()
    _print_labels_set(labels_set)


def _print_labels_set(labels: Set[Label]):
    for label in labels:
        print(indented_str("(", 2))
        print(indented_str(str(label), 4))
        print(indented_str(")", 2))
    print("========")


def _time_ordering(max_depth: int) -> List[Formula]:
    # \tau_0 <= \tau_1 <= ... <= \tau_{i / 2} <= \tau_max
    time_order: List[Formula] = list()

    for depth in range(1, max_depth + 1):
        iv = symbolic_interval(depth)
        time_order.append(inf(iv) <= sup(iv))

    last_iv = symbolic_interval(max_depth)
    time_order.append(sup(last_iv) <= tau_max())

    return time_order
