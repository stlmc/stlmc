import time

from .aux import *
from .graph import *
from .ha_converter import HAConverter
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

        # get an eps-strengthening reduced formula
        self._formula = strengthen_reduction(subst.substitute(self.formula), self.threshold)

        #
        self._optimizer = ContradictionChecker(self.tau_subst)
        self._label_generator = LabelGenerator(self._formula, threshold=self.threshold)
        self._graph_generator = GraphGenerator()
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
        bound = self.bound

        alg_s_t = time.time()
        init_labels = lg.init()
        init_labels = set(filter(lambda x: not self._optimizer.check_contradiction(x, 1, *_time_ordering(1)), init_labels))
        
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

                n = lg.expand(label, depth)
                n = set(filter(lambda x: not self._optimizer.check_contradiction(x, depth, *_time_ordering(depth)), n))
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

        ha = converter.convert(graph)
        # import pickle
        # with open("{}.graph".format("stl"), "wb") as fw:
        #     pickle.dump(graph, fw)
        # with open("{}.automata".format("stl"), "wb") as fw:
        #     pickle.dump(ha, fw)
        return ha


class GraphGenerator:
    def __init__(self):
        self.graph = Graph()
        self.node_id_dict: Dict[Tuple[Label, int], Node] = dict()

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
        node.non_intermediate, node.intermediate = split_label(label)

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


def _time_ordering(max_depth: int) -> List[Formula]:
    # 0 = \tau_0 <= \tau_1 <= ... <= \tau_{i / 2} <= \tau_max
    time_order: List[Formula] = [RealVal("0") == Real("tau_0")]

    for depth in range(1, max_depth + 1):
        iv = symbolic_interval(depth)
        time_order.append(inf(iv) <= sup(iv))

    last_iv = symbolic_interval(max_depth)
    time_order.append(sup(last_iv) <= tau_max())

    return time_order
