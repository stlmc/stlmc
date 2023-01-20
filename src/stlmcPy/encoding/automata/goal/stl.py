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
        jp_checker = JumpContradictionChecker()
        self._hybrid_converter.clear()
        alg_s_t = time.time()

        # get dummy initial node
        f_node = graph.first_node()

        # make initial labels
        init_label = Label(singleton(), singleton(), singleton(self._formula), singleton(),
                           set(), set(), set(), set(), set(), set(), 0)
        graph.open_label(f_node, init_label)

        waiting_list = [[graph.first_node()]]

        depth = 0
        while len(waiting_list) > 0:
            queue = waiting_list.pop(0)
            print("#{} -> {}".format(depth, len(queue)))

            # set upper bound of searching
            if depth >= self.bound:
                break

            new_queue = list()
            while len(queue) > 0:
                # pick a node and its labels
                p_n = queue.pop(0)
                label = graph.get_label(p_n)

                # expand the label
                lb_s = expand(label)
                for lb in lb_s:
                    is_initial = p_n == graph.first_node()
                    n = graph.make_node(lb, is_initial=is_initial)

                    exist, f_n, clk_subst = graph.find_node(n)
                    if exist:
                        # update clock variables at write positions and update clock renaming as resets
                        jp_c = {clk_subst.substitute(f, is_write=True) for f in lb.transition_cur}
                        jp_c.update(clk_subst.clock_assn())

                        # get used clocks and the clocks to be used
                        covered = graph.jump_write_clocks(jp_c)
                        should_be_covered = graph.jump_read_clocks(jp_c)
                        should_be_covered.update(graph.get_state_clocks(f_n))
                        missed = should_be_covered.difference(covered)

                        # make reset conditions for the uncovered clocks
                        identity = graph.identity_clk_subst(missed)
                        jp_c.update(identity.clock_assn())

                        jp = graph.make_jump(p_n, f_n, jp_c)
                        if jp_checker.is_contradiction(jp):
                            continue

                        graph.add_jump(jp)

                    else:
                        # get used clocks and the clocks to be used
                        covered = graph.jump_write_clocks(lb.transition_cur)
                        should_be_covered = graph.jump_read_clocks(lb.transition_cur)
                        should_be_covered.update(graph.get_state_clocks(n))
                        missed = should_be_covered.difference(covered)

                        # make identity reset conditions for the uncovered clocks
                        identity = graph.identity_clk_subst(missed)
                        jp_c = lb.transition_cur
                        jp_c.update(identity.clock_assn())

                        # make node and check its contradiction
                        jp = graph.make_jump(p_n, n, jp_c)
                        if jp_checker.is_contradiction(jp):
                            continue

                        # add a fresh node and open the label
                        # add the state to the queue when it is reachable
                        graph.add_node(n)
                        graph.open_label(n, lb)
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

        s_t_s = time.time()
        graph.remove_self_loop()
        e_t_s = time.time()
        print("after removing self loop ({:.3f}s)".format(e_t_s - s_t_s))
        print(print_graph_info(graph))

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
