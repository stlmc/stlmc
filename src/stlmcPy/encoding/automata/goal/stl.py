import time

from .aux import *
from .equivalence import PPEquivalence
from .graph import *
from .ha_converter import HAConverter
from .label import *
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
        self._hybrid_converter = HAConverter(self.tau_subst)

    def encode(self):
        graph: TableauGraph = TableauGraph(self._formula)
        self._hybrid_converter.clear()
        alg_s_t = time.time()

        # get dummy initial node
        f_node = graph.first_node()

        # make initial labels
        init_label = Label(singleton(), singleton(), singleton(self._formula), singleton(), set(), set(), 0)
        lb_s = expand(init_label)

        # make initial nodes
        initial_nodes = list()
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
                initial_nodes.append(node)

        waiting_list = [initial_nodes]

        depth = 1
        while len(waiting_list) > 0:
            queue = waiting_list.pop(0)
            print("#{} -> {}".format(depth, len(queue)))

            new_queue = list()
            while len(queue) > 0:

                # pick a node and its labels
                p_n = queue.pop(0)
                labels = graph.get_labels(p_n)

                # make nodes
                for lb in labels:
                    # expand the label
                    lb_s = expand(lb)
                    for e_lb in lb_s:
                        n = graph.make_node(e_lb)

                        exist, f_n, clk_subst = graph.find_node(n)
                        if exist:
                            # update the label and type hint clocks
                            u_lb = graph.update_label_clock(e_lb, clk_subst)

                            jp_s = graph.make_jumps(p_n, f_n, u_lb)
                            for jp in jp_s:
                                graph.add_jump(jp)

                        else:
                            # add a fresh node and open the label
                            graph.add_node(n)
                            graph.open_labels(n, e_lb)

                            jp_s = graph.make_jumps(p_n, n, e_lb)
                            for jp in jp_s:
                                graph.add_jump(jp)
                            new_queue.append(n)

            # if new states are generated, add it to the queue
            if len(new_queue) > 0:
                waiting_list.append(new_queue)
            depth += 1

        alg_e_t = time.time()
        print("running time: {:.3f}s".format(alg_e_t - alg_s_t))

        print_graph_info(graph)

        u_t_s = time.time()
        graph.remove_unreachable()
        u_t_e = time.time()
        print("after remove unreachable states ({:.3f}s)".format(u_t_e - u_t_s))
        print_graph_info(graph)

        p_t_s = time.time()
        post_eq = PPEquivalence()
        post_eq.reduce(graph)
        p_t_e = time.time()

        print("after pp equivalence ({:.3f}s)".format(p_t_e - p_t_s))
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
