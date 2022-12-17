import time

from .aux import *
from .equivalence import StutteringEquivalenceChecker
from .graph import *
from .ha_converter import HAConverter
from .label import *
from .subsumption import ForwardSubsumption, BackwardSubsumption, PathSubsumption
from ...smt.goal.aux import *
from ....constraints.aux.operations import *
from ....hybrid_automaton.hybrid_automaton import *
from ....objects.goal import Goal


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
        # self._optimizer = ContradictionChecker(self.clk_subst_dict, self.tau_subst)
        # self._label_generator = LabelGenerator(self._formula, threshold=self.threshold)
        # self._stuttering_checker = StutteringEquivalenceChecker(self._formula)
        # self._shifting_checker = ShiftingEquivalenceChecker(self._formula)
        # self._graph_generator = GraphGenerator(self._formula, self._optimizer, self._shifting_checker, shift_mode=True)
        self._hybrid_converter = HAConverter(self.tau_subst)

        self._forward_subsumption = ForwardSubsumption()
        self._backward_subsumption = BackwardSubsumption()
        self._path_subsumption = PathSubsumption(self._forward_subsumption.get_relation(),
                                                 self._backward_subsumption.get_relation())

    def encode(self):
        graph: TableauGraph = TableauGraph(self._formula)
        st_checker = StutteringEquivalenceChecker(self._formula)
        self._hybrid_converter.clear()
        alg_s_t = time.time()

        # get dummy initial node
        f_node = graph.first_node()

        # make initial labels
        init_label = Label(singleton(), singleton(), singleton(self._formula), singleton())
        lb_s = expand(init_label)

        # make initial nodes
        initial_nodes = set()
        for lb in lb_s:
            # make a new node
            node = graph.make_node(lb, is_initial=True)

            # check if already exists
            exist, f_n, clk_subst = graph.find_node(node)
            if exist:
                # update the label and type hint clocks
                u_lb = graph.update_label_clock(lb, clk_subst)

                jp_s = graph.make_jumps(f_node, f_n, u_lb)
                for jp in jp_s:
                    graph.add_jump(jp)

                # still not finished but already exists
                # open the label to the node
                graph.open_labels(f_n, u_lb)
            else:
                # add a fresh node and open the label
                graph.add_node(node)
                graph.open_labels(node, lb)

                jp_s = graph.make_jumps(f_node, node, lb)
                for jp in jp_s:
                    graph.add_jump(jp)
                initial_nodes.add(node)

        waiting_list = initial_nodes
        finished = set()

        loop = 0
        while len(waiting_list) > 0:
            print("#{} -> {}".format(loop, len(graph.get_nodes())))

            # pick a node and its labels
            p_n = waiting_list.pop()

            labels = graph.get_labels(p_n)

            # make nodes
            for lb in labels:
                # expand the label
                lb_s = expand(lb)
                for e_lb in lb_s:
                    # remove stuttering
                    if st_checker.equivalent(lb, e_lb):
                        continue

                    n = graph.make_node(e_lb)

                    exist, f_n, clk_subst = graph.find_node(n)
                    if exist:
                        # update the label and type hint clocks
                        u_lb = graph.update_label_clock(e_lb, clk_subst)

                        jp_s = graph.make_jumps(p_n, f_n, u_lb)
                        for jp in jp_s:
                            graph.add_jump(jp)

                        # still not finished but already exists, and it is not finished
                        if f_n not in finished:
                            # open the label to the node
                            graph.open_labels(f_n, u_lb)
                    else:
                        # add a fresh node and open the label
                        graph.add_node(n)
                        graph.open_labels(n, e_lb)

                        jp_s = graph.make_jumps(p_n, n, e_lb)
                        for jp in jp_s:
                            graph.add_jump(jp)
                        waiting_list.add(n)

            finished.add(p_n)
            loop += 1

        # print(graph.first_node())
        # print()
        # print(graph)
        # init_labels = lg.init()
        # init_labels = set(filter(lambda x: not self._optimizer.check_contradiction(x, 1, *_time_ordering(graph.get_max_depth())), init_labels))

        # make initial nodes
        # for label in init_labels:
        #     self._graph_generator.make_node(label)
        # self._graph_generator.finish_depth()

        # wait_queue: Set[Label] = init_labels
        # next_queue: Set[Label] = set()

        # total_label = len(init_labels)
        # total_nodes = len(graph.get_nodes_at(1))
        # depth, final_depth = 2, bound
        # while True:
        #     if depth > final_depth:
        #         break

        # s = time.time()
        # # print("depth : {}".format(depth))
        # for label in wait_queue:
        #     # check
        #     # print("  label: {}".format(label))
        #     if self._optimizer.check_contradiction(label, depth):
        #         continue
        #
        #     n = lg.expand(label, depth)
        #     n = set(filter(lambda x: not self._optimizer.check_contradiction(x, depth, *_time_ordering(graph.get_max_depth())), n))
        #     # n = self._apply_reduction(n)
        #     n = st_checker.stuttering(label, n)
        #
        #     next_queue.update(n)
        #     # next_queue = canonicalize(next_queue)
        #     # print_extend(label, n)
        #
        #     if final_depth >= depth:
        #         self._graph_generator.make_posts(label, n)
        #
        # e = time.time()
        # wait_queue = next_queue.copy()
        # # wait_queue = self._apply_reduction(next_queue)
        # next_queue.clear()

        #
        # if depth <= graph.get_max_depth():
        #     cur_nodes = len(graph.get_nodes_at(depth))
        # else:
        #     cur_nodes = 0

        # num_labels = len(wait_queue)
        # total_label += num_labels
        # total_nodes += cur_nodes

        # print("depth#{}, labels#{}, labelsAcc#{}, nodes#{}, nodesAcc#{}".format(depth,
        #                                                                         num_labels,
        #                                                                         total_label,
        #                                                                         cur_nodes,
        #                                                                         total_nodes))
        # logging = ["translate: {:.3f}".format(self._optimizer.translate_time),
        #            "contradiction: {:.3f}".format(self._optimizer.contradiction_time),
        #            "contradiction call# {}".format(self._optimizer.contradiction_call),
        #            "solver time: {:.3f}".format(self._optimizer.z3obj_time),
        #            "total: {:.3f}".format(e - s)]
        #
        # print("{}".format("\n".join(map(lambda x: indented_str(x, 2), logging))))
        # self._optimizer.time_clear()
        # self._graph_generator.finish_depth()
        # depth += 1

        # self._graph_generator.remove_contradiction()
        # self._graph_generator.make_shift_resets()
        # self._graph_generator.remove_redundancy()
        alg_e_t = time.time()
        print("running time: {:.3f}s".format(alg_e_t - alg_s_t))
        # print_graph_info(graph)
        # _tableau.add_shift_resets()
        # _tableau.remove_unreachable()
        # print_graph_info(_tableau.graph)

        # print("after remove unreachable")
        # s_t = time.time()
        # self._graph_generator.remove_unreachable()
        # e_t = time.time()
        # print("unreach remove : {:.3f}s".format(e_t - s_t))
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

        # ha = self._hybrid_converter.convert(graph)

        # print(graph)
        # print_ha_size("ha", ha)
        # import pickle
        # with open("{}.graph".format("stl"), "wb") as fw:
        #     pickle.dump(graph, fw)
        # with open("{}.automata".format("stl"), "wb") as fw:
        #     pickle.dump(ha, fw)
        # return ha


def print_wait_queue(wait_queue: Set[Label]):
    print()
    print("lb wait queue >")
    for p_l in wait_queue:
        print(indented_str(str(p_l), 2))


def print_graph_info(graph: TableauGraph):
    print("v#{}, e#{}".format(len(graph.get_nodes()), len(get_node_jumps(graph))))


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
