import time

from .aux import *
from .graph import *
from .optimizer import PropositionOptimizer
from .subsumption import ForwardSubsumption, BackwardSubsumption, PathSubsumption
from ...smt.goal.aux import *
from ....constraints.aux.operations import *
from ....hybrid_automaton.hybrid_automaton import *
from ....hybrid_automaton.utils import make_jump
from ....objects.goal import Goal
from ....util.printer import indented_str
from .label import *


# import xml.etree.ElementTree as ElemT


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

        # update_sub_formula(self.sub_formulas)

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
        self._optimizer = PropositionOptimizer(self.tau_subst)
        self._graph_generator = GraphGenerator(self.tau_subst, self._optimizer)

        self._expand_cache: Dict[Label, Set[Label]] = dict()
        # self._extend_cache1: Dict[LabelInfo, Set[Labels]] = dict()
        # self._extend_cache2: Dict[LabelInfo, Set[Labels]] = dict()

        self._forward_subsumption = ForwardSubsumption()
        self._backward_subsumption = BackwardSubsumption()
        self._path_subsumption = PathSubsumption(self._forward_subsumption.get_relation(),
                                                 self._backward_subsumption.get_relation())

    def encode(self):
        self._graph_generator.clear()
        graph = self._graph_generator.graph
        bound = self.bound
        print(self.st_formula)

        alg_s_t = time.time()
        init_labels = init(self.st_formula, self._expand_cache)
        init_labels = set(filter(lambda x: not self._optimizer.check_contradiction(x, 1), init_labels))

        # make initial nodes
        for label in init_labels:
            self._graph_generator.make_node(label, 1)

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

                n = expand(label, depth, self._expand_cache)
                n = set(filter(lambda x: not self._optimizer.check_contradiction(x, depth), n))
                # n = self._apply_reduction(n)
                n = stuttering(label, n, depth)

                next_queue.update(n)
                # next_queue = canonicalize(next_queue)
                # print_extend(label, n)

                if final_depth >= depth:
                    self._graph_generator.make_posts(label, n, depth)

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
                       "reduction time: {:.3f}".format(self._optimizer.reduction_time),
                       "solver time: {:.3f}".format(self._optimizer.z3obj_time),
                       "total: {:.3f}".format(e - s)]

            print("{}".format("\n".join(map(lambda x: indented_str(x, 2), logging))))
            self._optimizer.time_clear()
            depth += 1

        alg_e_t = time.time()
        print("running time: {:.3f}s".format(alg_e_t - alg_s_t))

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

        return _graph2ha(graph, self.tau_subst)

    def _apply_reduction(self, labels_set: Set[Label]):
        n_labels = set(filter(lambda x: not self._optimizer.check_contradiction(x), labels_set))
        self._optimizer.calc_label_reduction(*n_labels, assumptions=self._time_order.children)
        return canonicalize(*n_labels)


class GraphGenerator:
    def __init__(self, tau_subst: VarSubstitution,
                 prop_optimizer: PropositionOptimizer):
        self.graph = Graph()
        self.node_id_dict: Dict[Tuple[Label, int], Node] = dict()
        self._optimizer = prop_optimizer
        self._tau_subst = tau_subst

    def clear(self):
        self.graph = Graph()
        self.node_id_dict = dict()

    def make_posts(self, parent_label: Label, post_labels: Set[Label], depth: int):
        post_nodes = set()
        for post in post_labels:
            # do not make node for empty label
            if not is_empty_labels(post):
                post_nodes.add(self.make_node(post, depth))

        # if parent
        if (parent_label, depth - 1) in self.node_id_dict:
            parent = self.node_id_dict[(parent_label, depth - 1)]

            for node in post_nodes:
                connect(parent, node)
        else:
            raise Exception("labels should have a parent")

    def make_node(self, label: Label, depth: int):
        # do not make node for empty label
        if is_empty_labels(label):
            raise Exception("label cannot be empty")

        # if node is already exists
        if label in self.node_id_dict:
            return self.node_id_dict[(label, depth)]

        node = Node(hash(label), depth)
        non_intermediate, intermediate = translate(label, depth)
        non_intermediate = set(map(lambda x: self._tau_subst.substitute(x), non_intermediate))
        node.non_intermediate, node.intermediate = non_intermediate, intermediate

        self.graph.add_node(node)
        self.node_id_dict[(label, depth)] = node

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

    def apply_prop_reduction(self):
        for node in self.graph.nodes:
            labels = frozenset(node.non_intermediate.union(node.intermediate))
            non_intermediate, intermediate = self._optimizer.reduce_label(labels)
            node.non_intermediate, node.intermediate = frozenset(non_intermediate), frozenset(intermediate)


def is_empty_labels(label: Label):
    return len(label.cur) == 0


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


def _is_final_label(label: Label):
    return len(label.nxt) == 0


def _is_initial_node(node: Node):
    return node.depth == 1


# def print_wait_queue(wait_queue: List[Tuple[Set[Formula], Label]]):
#     print()
#     print("lb wait queue >")
#     for p_c, p_l in wait_queue:
#         print(indented_str("\n".join([indented_str(str(f), 4) for f in p_c]), 2))
#         print(indented_str(str(p_l), 2))

def print_wait_queue(wait_queue: Set[Label]):
    print()
    print("lb wait queue >")
    for p_l in wait_queue:
        print(indented_str(str(p_l), 2))


def print_graph_info(graph: Graph):
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


def _graph2ha(graph: Graph, tau_subst: VarSubstitution):
    automata = HybridAutomaton()
    max_depth = graph.get_max_depth()

    init_mode = Mode(0)
    # automata.add_mode("init_mode")
    zero_time_dyns = _zero_time_dynamics(max_depth)
    init_mode.add_dynamic(*zero_time_dyns)
    init_mode.set_as_initial()

    node2mode_dict: Dict[Node, Mode] = dict()
    time_dyns_dict = _time_dynamics(max_depth)
    init_cond = _time_init_cond(max_depth)
    time_rsts = _time_resets(max_depth)

    automata.add_init(*init_cond)

    time_guard: Dict[Mode, Set[Formula]] = dict()

    for index, node in enumerate(graph.nodes):
        mode = Mode(index + 1)
        mode.add_dynamic(*time_dyns_dict[node.depth])

        if node.is_final():
            mode.set_as_final()

        if node.is_initial():
            mode.set_as_initial()

        # set inv
        for label in node.non_intermediate:
            if is_timed_label(label):
                t_f = tau_subst.substitute(translate(label))
                if mode in time_guard:
                    time_guard[mode].add(t_f)
                else:
                    time_guard[mode] = {t_f}
            else:
                mode.add_invariant(translate(label))

        automata.add_mode(mode)
        node2mode_dict[node] = mode

    for node in graph.nodes:
        mode = node2mode_dict[node]

        for p_node in node.pred:
            p_mode = node2mode_dict[p_node]
            jp = make_jump(p_mode, mode)
            jp.add_reset(*time_rsts)

        for s_node in node.succ:
            s_mode = node2mode_dict[s_node]
            jp = make_jump(mode, s_mode)
            jp.add_reset(*time_rsts)

    # print(time_guard)
    # move time guard to the next jump
    empty_final_mode = Mode(-10)
    empty_final_mode.add_dynamic(*zero_time_dyns)
    empty_final_mode.set_as_final()
    is_empty_final_needed = False

    for mode in time_guard:
        t_fs = time_guard[mode]
        if mode.is_final():
            is_empty_final_needed = True
            mode.set_as_non_final()
            jp = make_jump(mode, empty_final_mode)
            jp.add_guard(*t_fs)
        else:
            for m in mode.s_jumps:
                s_jps = mode.s_jumps[m]
                for jp in s_jps:
                    jp.add_guard(*t_fs)

    if is_empty_final_needed:
        automata.add_mode(empty_final_mode)

    return automata


def _time_init_cond(max_depth: int) -> Set[Formula]:
    s = set()
    time_vars: List[Real] = _time_variables(max_depth)
    zero = RealVal("0.0")
    for v in time_vars:
        s.add(v == zero)
    return s


def _time_ordering(max_depth: int) -> And:
    # 0 = \tau_0 <= \tau_1 <= ... <= \tau_{i / 2} <= \tau_max
    time_order: List[Formula] = [RealVal("0") == Real("tau_0")]

    for depth in range(1, max_depth + 1):
        iv = symbolic_interval(depth)
        time_order.append(inf(iv) <= sup(iv))

    last_iv = symbolic_interval(max_depth)
    time_order.append(sup(last_iv) <= tau_max())

    return And(time_order)


def _time_dynamics(max_depth: int) -> Dict[int, Set[Tuple[Real, Expr]]]:
    time_dict: Dict[int, Set[Tuple[Real, Expr]]] = dict()
    cur_depth = 1
    while max_depth >= cur_depth:
        time_dict[cur_depth] = _time_dynamics_at(cur_depth, max_depth)
        cur_depth += 1

    return time_dict


def _time_dynamics_at(cur_depth: int, max_depth: int) -> Set[Tuple[Real, Expr]]:
    time_dyns: Set[Tuple[Real, Expr]] = set()
    zero, one = RealVal("0.0"), RealVal("1.0")

    depth = 1
    while max_depth >= depth:
        s_v, e_v = partition_inf(depth), partition_sup(depth)

        if depth < cur_depth:
            time_dyns.update({(s_v, zero), (e_v, zero)})

        elif depth == cur_depth:
            time_dyns.update({(s_v, zero), (e_v, one)})
        else:
            time_dyns.update({(s_v, one), (e_v, one)})

        depth += 1

    return time_dyns


def _zero_time_dynamics(max_depth: int) -> Set[Tuple[Real, Expr]]:
    time_vars: List[Real] = _time_variables(max_depth)
    time_dyns: Set[Tuple[Real, Expr]] = set()

    zero = RealVal("0.0")
    for v in time_vars:
        time_dyns.add((v, zero))

    return time_dyns


def _time_resets(max_depth: int) -> Set[Tuple[Variable, Expr]]:
    time_vars: List[Real] = _time_variables(max_depth)
    time_rsts: Set[Tuple[Variable, Expr]] = set()

    for time_v in time_vars:
        time_rsts.add((time_v, time_v))

    return time_rsts


def _time_variables(max_depth: int) -> List[Real]:
    time_vars: Set[Real] = set()
    cur_depth = 1
    while True:
        if cur_depth > max_depth:
            break
        time_vars.update({partition_inf(cur_depth), partition_sup(cur_depth)})

        cur_depth += 1

    return sorted(time_vars, key=lambda x: x.id)


