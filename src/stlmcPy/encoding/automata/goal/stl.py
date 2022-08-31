import functools
import time
from typing import Any

from z3 import z3

from .aux import *
from .optimizer import PropositionOptimizer
from .subsumption import ForwardSubsumption, BackwardSubsumption, PathSubsumption
from ...smt.goal.aux import *
from ....constraints.aux.operations import *
from ....hybrid_automaton.hybrid_automaton import *
from ....objects.goal import Goal
from ....objects.graph import *
from ....util.printer import indented_str
import xml.etree.ElementTree as ElemT


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

        # get an eps-strengthening reduced formula
        self.st_formula = strengthen_reduction(subst.substitute(self.formula), self.threshold)
        self.sub_formulas = calc_sub_formulas(self.st_formula)

        update_sub_formula(self.sub_formulas)

        #
        self._hash_dict: Dict[hash, Formula] = dict()
        self._interval_hash_dict: Dict[hash, Interval] = dict()

        print("===============")
        print("subformula of {}".format(indented_str(str(self.st_formula), 0)))
        for idx, f in enumerate(self.sub_formulas):
            self._hash_dict[hash(f)] = f
            if isinstance(f, Temporal):
                self._interval_hash_dict[hash(f.local_time)] = f.local_time
            print(indented_str("#{}: {} --> {}".format(idx, f, hash(f)), 2))
        print("===============")

        print("time ordering")
        self._time_order = _time_ordering(2 * self.bound + 2)
        print(self._time_order)

        #
        self._optimizer = PropositionOptimizer(self.tau_subst, self._hash_dict, self._interval_hash_dict)
        self._graph_generator = GraphGenerator(self._hash_dict, self._interval_hash_dict, self._optimizer)
        self._extend_cache: Dict[Label, LabelSet] = dict()
        self._forward_subsumption = ForwardSubsumption()
        self._backward_subsumption = BackwardSubsumption()
        self._path_subsumption = PathSubsumption(self._forward_subsumption.get_relation(),
                                                 self._backward_subsumption.get_relation())

    def encode(self):
        self._graph_generator.clear()
        bound = self.bound
        print(self.st_formula)

        alg_s_t = time.time()
        init_labels = init(self.st_formula)
        # make initial nodes
        for label in init_labels:
            # TODO
            if self._optimizer.check_contradiction(label):
                continue

            self._optimizer.calc_label_reduction(label)
            self._graph_generator.make_node(label, 1)

        wait_queue: LabelSet = init_labels
        next_queue: LabelSet = set()
        # wait_queue = [init_labels]
        # next_queue = list()

        total_label = 0
        total_nodes = 0
        depth, final_depth = 1, 2 * bound + 2
        while True:
            if depth > final_depth:
                break

            # if depth == 5:
            #     print(len(wait_queue))
            #     for ll in wait_queue:
            #         print(ll)

            s = time.time()
            num_labels = len(wait_queue)
            # print("depth : {}".format(depth))
            for label in wait_queue:
                # check
                # print("  label: {}".format(label))
                if self._optimizer.check_contradiction(label):
                    continue

                if label in self._extend_cache:
                    n = self._extend_cache[label]
                else:
                    n = expand(label, self._hash_dict)
                    # TODO
                    for la in n.copy():
                        if self._optimizer.check_contradiction(la):
                            n.discard(la)

                    self._extend_cache[label] = n

                next_queue.update(n)
                # print("label : {} --> {}".format(label, n))

                if final_depth > depth:
                    self._graph_generator.make_posts(label, n, depth + 1)

                # calculate label reduction
                self._optimizer.calc_label_reduction(label)
                self._optimizer.calc_label_reduction(*next_queue)

            e = time.time()
            wait_queue = next_queue.copy()
            next_queue.clear()
            cur_nodes = len(self._graph_generator.graph.get_nodes_at(depth))

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
                       "reduction time: {:.3f}".format(self._optimizer.reduction_time),
                       "solver time: {:.3f}".format(self._optimizer.z3obj_time),
                       "total: {:.3f}".format(e - s)]

            print("{}".format("\n".join(map(lambda x: indented_str(x, 2), logging))))
            self._optimizer.time_clear()
            depth += 1

        alg_e_t = time.time()
        print("wow")
        print("running time: {:.3f}s".format(alg_e_t - alg_s_t))

        graph = self._graph_generator.graph
        print_graph_info(graph)

        print("after remove unreachable")
        s_t = time.time()
        self._graph_generator.remove_unreachable()
        e_t = time.time()
        print("unreach remove : {:.3f}s".format(e_t - s_t))
        print_graph_info(graph)

        print("reduce proposition")
        self._graph_generator.apply_prop_reduction()
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

        print(graph)
        # test_graph = Graph()
        # case 1)
        # node1 = Node(1, 1)
        # node1.ap = {chi(1, 1, Bool("p"))}
        # node2 = Node(2, 1)
        # node2.ap = {chi(1, 1, Bool("p")), chi(1, 1, Bool("q"))}
        # node3 = Node(3, 1)
        # node3.ap = {chi(1, 1, Bool("q"))}
        # node4 = Node(4, 1)
        # node4.ap = {chi(1, 1, Bool("a"))}
        # nodes = [node1, node2, node3, node4]

        # case 2)
        # node1 = Node(1, 1)
        # node1.ap = {chi(1, 1, Bool("p"))}
        # node2 = Node(2, 1)
        # node2.ap = {chi(1, 1, Bool("p"))}
        # node3 = Node(3, 1)
        # node3.ap = {chi(1, 1, Bool("p"))}
        # node4 = Node(4, 1)
        # node4.ap = {chi(1, 1, Bool("p"))}
        # nodes = [node1, node2, node3, node4]

        # case 3)
        # node1 = Node(1, 1)
        # node1.ap = {chi(1, 1, Bool("p"))}
        # node2 = Node(2, 1)
        # node2.ap = {chi(1, 1, Bool("q"))}
        # node3 = Node(3, 1)
        # node3.ap = {chi(1, 1, Bool("r"))}
        # node4 = Node(4, 1)
        # node4.ap = {chi(1, 1, Bool("s"))}
        # nodes = [node1, node2, node3, node4]
        # for node in nodes:
        #     node.set_as_initial()
        #     # node.ap = {chi(1, 1, Bool("wow{}".format(ix)))}
        #
        #     test_graph.add_node(node)
        #
        # self._forward_subsumption.calc_relation(test_graph)

        # print("after backward equiv")
        # self._graph_generator.backward_equiv()
        # print_graph_info(graph)

        return _graph2ha(graph, self.tau_subst, self._hash_dict, self._interval_hash_dict)


class GraphGenerator:
    def __init__(self, hash_dict1: Dict[hash, Formula], hash_dict2: Dict[hash, Interval],
                 prop_optimizer: PropositionOptimizer):
        self.graph = Graph()
        self.node_id_dict: Dict[Label, Node] = dict()
        self._hash_dict1 = hash_dict1
        self._hash_dict2 = hash_dict2
        self._optimizer = prop_optimizer

    def clear(self):
        self.graph = Graph()
        self.node_id_dict = dict()

    def make_posts(self, parent_label: Label, post_labels: LabelSet, depth: int):
        post_nodes = set()
        for post in post_labels:
            # do not make node for empty label
            if not is_empty_label(post):
                post_nodes.add(self.make_node(post, depth))

        # if parent
        if parent_label in self.node_id_dict:
            parent = self.node_id_dict[parent_label]

            for node in post_nodes:
                connect(parent, node)

    def make_node(self, label: Label, depth: int):
        # do not make node for empty label
        if is_empty_label(label):
            return

        # if node is already exists
        if label in self.node_id_dict:
            return self.node_id_dict[label]

        node = Node(hash(label), depth)
        node.ap, node.non_ap = split_label(label, self._hash_dict1)

        self.graph.add_node(node)
        self.node_id_dict[label] = node

        if _is_final_node(node):
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

    def apply_prop_reduction(self):
        for node in self.graph.nodes:
            label = frozenset(node.ap.union(node.non_ap))
            node.ap, node.non_ap = self._optimizer.reduce_label(label)


def is_empty_label(label: Label):
    return len(label) == 0


def _find_reachable(graph: Graph) -> Set[Node]:
    reach: Set[Node] = set()

    max_depth = graph.get_max_depth()
    cur_depth = max_depth
    while cur_depth > 0:
        nodes = graph.get_nodes_at(cur_depth)

        for node in nodes:
            # final is reachable
            if node.is_final():
                reach.add(node)
            else:
                # else at least one successor is reachable
                if len(node.succ.intersection(reach)) > 0:
                    reach.add(node)

        cur_depth -= 1

    return reach


def _is_final_node(node: Node):
    return len(node.non_ap) == 0


def _is_initial_node(node: Node):
    return node.depth == 1


def print_graph_info(graph: Graph):
    print("graph size #{}".format(len(graph.nodes)))
    for d in range(graph.get_max_depth()):
        print("depth@{} --> graph node#{}".format(d + 1, len(graph.get_nodes_at(d + 1))))
        # for index, node in enumerate(graph.get_nodes_at(d + 1)):
        #     print(indented_str("node{} --> pred: {}, succ: {}".format(index, len(node.pred), len(node.succ)), 2))


def _graph2ha(graph: Graph, tau_subst: VarSubstitution,
              hash_dict1: Dict[hash, Formula], hash_dict2: Dict[hash, Interval]):
    automata = HybridAutomaton("stl_ha_{}".format(id(graph)))
    max_depth = graph.get_max_depth()

    init_mode = automata.add_mode("init_mode")
    init_time_dyns = _init_time_dynamics(max_depth)
    init_mode.set_dynamic(*init_time_dyns)
    automata.mark_initial(init_mode)

    node2mode_dict: Dict[Node, Mode] = dict()
    time_dyns = _time_dynamics(max_depth)
    init_cond = _time_init_cond(max_depth)

    automata.initial_conditions.update(init_cond)

    cur_depth = 2
    while True:
        if cur_depth > max_depth:
            break

        nodes = graph.get_nodes_at(cur_depth)
        for index, node in enumerate(nodes):
            mode = automata.add_mode("mode@{}${}".format(cur_depth, index))
            mode.set_invariant(*translate(node.ap, tau_subst, hash_dict1, hash_dict2))
            mode.set_dynamic(*time_dyns)
            node2mode_dict[node] = mode

            if node.is_initial():
                automata.mark_initial(mode)

            if node.is_final():
                automata.mark_final(mode)
                _add_final_time_inv(mode, cur_depth, tau_subst)

        cur_depth += 2

    cur_depth = 1
    while True:
        if cur_depth > max_depth:
            break

        time_rsts = _time_resets(cur_depth, max_depth)

        final_mode = automata.add_mode("f_mode@{}".format(cur_depth + 1))
        _add_final_time_inv(final_mode, cur_depth + 1, tau_subst)
        nodes = graph.get_nodes_at(cur_depth)

        for index1, node in enumerate(nodes):
            guards = translate(node.ap, tau_subst, hash_dict1, hash_dict2)
            if node.is_initial() and node.is_final():
                jp = automata.add_transition("jp@{}${}".format(cur_depth, index1), init_mode, final_mode)
                jp.set_guard(*guards)
                jp.set_reset(*time_rsts)
            elif node.is_initial():
                for index2, s in enumerate(node.succ):
                    s_mode = node2mode_dict[s]
                    jp = automata.add_transition("jp@{}${}_{}".format(cur_depth, index1, index2), init_mode, s_mode)
                    jp.set_guard(*guards)
                    jp.set_reset(*time_rsts)
            elif node.is_final():
                for index2, p in enumerate(node.pred):
                    p_mode = node2mode_dict[p]
                    jp = automata.add_transition("jp@{}${}_{}".format(cur_depth, index1, index2), p_mode, final_mode)
                    jp.set_guard(*guards)
                    jp.set_reset(*time_rsts)
            else:
                for index2, (p, s) in enumerate(set(product(node.pred, node.succ))):
                    p_mode, s_mode = node2mode_dict[p], node2mode_dict[s]
                    jp = automata.add_transition("jp@{}${}_{}".format(cur_depth, index1, index2), p_mode, s_mode)
                    jp.set_guard(*guards)
                    jp.set_reset(*time_rsts)

        if len(final_mode.incoming) == 0 and len(final_mode.outgoing) == 0:
            automata.remove_mode(final_mode)
        else:
            automata.mark_final(final_mode)

        cur_depth += 2

    return automata


# def _time_dynamics(cur_depth: int, max_depth: int) -> Set[Tuple[Real, Expr]]:
#     time_dict: Dict[Real, Expr] = dict()
#     time_vars: List[Real] = _time_variables(max_depth)
#     time_dyns: Set[Tuple[Real, Expr]] = {(Real("clk"), RealVal("1.0"))}
#
#     zero, one = RealVal("0.0"), RealVal("1.0")
#     inf, sup = symbolic_inf(cur_depth), symbolic_sup(cur_depth)
#     for time_v in time_vars:
#         if variable_equal(inf, time_v):
#             time_dict[time_v] = one
#         else:
#             time_dict[time_v] = zero
#
#         if variable_equal(sup, time_v):
#             time_dict[time_v] = one
#         else:
#             time_dict[time_v] = zero
#
#     for v in time_dict:
#         time_dyns.add((v, time_dict[v]))
#
#     return time_dyns

def _time_init_cond(max_depth: int) -> Set[Formula]:
    s = {_global_clk() == RealVal("0.0")}
    time_vars: List[Real] = _time_variables(max_depth)
    zero = RealVal("0.0")
    for v in time_vars:
        s.add(v == zero)
    return s


def _time_ordering(max_depth: int) -> And:
    assert max_depth % 2 == 0
    # 0 = \tau_0 < \tau_1 < ... < \tau_{i / 2} <= \tau_max
    time_order: List[Formula] = [RealVal("0") == Real("tau_0")]

    for depth in range(2, max_depth + 1, 2):
        assert depth % 2 == 0
        time_order.append(symbolic_inf(depth) < symbolic_sup(depth))

    time_order.append(symbolic_sup(max_depth) <= tau_max())

    return And(time_order)


def _time_dynamics(max_depth: int) -> Set[Tuple[Real, Expr]]:
    time_vars: List[Real] = _time_variables(max_depth)
    time_dyns: Set[Tuple[Real, Expr]] = {(_global_clk(), RealVal("1.0"))}

    zero = RealVal("0.0")
    for v in time_vars:
        time_dyns.add((v, zero))

    return time_dyns


def _init_time_dynamics(max_depth: int) -> Set[Tuple[Real, Expr]]:
    time_vars: List[Real] = _time_variables(max_depth)
    time_dyns: Set[Tuple[Real, Expr]] = {(_global_clk(), RealVal("0.0"))}

    zero = RealVal("0.0")
    for v in time_vars:
        time_dyns.add((v, zero))

    return time_dyns


def _time_resets(cur_depth: int, max_depth: int) -> Set[Tuple[Variable, Expr]]:
    time_vars: List[Real] = _time_variables(max_depth)
    time_dict: Dict[Variable, Expr] = dict()
    time_rsts: Set[Tuple[Variable, Expr]] = set()

    inf = symbolic_inf(cur_depth)
    for time_v in time_vars:
        if variable_equal(inf, time_v):
            time_dict[time_v] = _global_clk()
        else:
            time_dict[time_v] = time_v

    for v in time_dict:
        time_rsts.add((v, time_dict[v]))

    return time_rsts


def _time_variables(max_depth: int) -> List[Real]:
    time_vars: Set[Real] = set()
    cur_depth = 1
    while True:
        if cur_depth > max_depth:
            break
        time_vars.update({symbolic_inf(cur_depth), symbolic_sup(cur_depth)})

        cur_depth += 1

    return sorted(time_vars, key=lambda x: x.id)


def _add_final_time_inv(mode: Mode, cur_depth: int, tau_subst: VarSubstitution):
    mode.set_invariant(tau_subst.substitute(symbolic_inf(cur_depth) == tau_max()))


def _global_clk():
    return Real("clk")
