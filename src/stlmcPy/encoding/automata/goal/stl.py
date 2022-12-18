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

        alg_e_t = time.time()
        print("running time: {:.3f}s".format(alg_e_t - alg_s_t))

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

        ha = self._hybrid_converter.convert(graph)

        # print(graph)
        # print_ha_size("ha", ha)
        # import pickle
        # with open("{}.graph".format("stl"), "wb") as fw:
        #     pickle.dump(graph, fw)
        # with open("{}.automata".format("stl"), "wb") as fw:
        #     pickle.dump(ha, fw)
        return ha


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
