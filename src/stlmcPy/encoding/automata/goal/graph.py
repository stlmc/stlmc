from typing import FrozenSet, List, Optional

from .aux import expand, init, split_label, symbolic_interval
from .clock import global_clk, time_variables
from .equivalence import ShiftingEquivalenceChecker, StutteringEquivalenceChecker
from .label import Label
from ....constraints.aux.operations import inf, sup, variable_equal
from ....constraints.constraints import Real, Formula
from ....graph.graph import *
from ....util.printer import indented_str


class TableauGenerator:
    def __init__(self, formula: Formula, **args):
        if "threshold" in args:
            self._threshold = float(args["threshold"])
        else:
            raise Exception("threshold should be given")

        # label
        self._formula: Formula = formula
        self._depth: int = 0
        self._next_nodes: Set[Node] = set()

        # graph
        self.graph: TableauGraph = TableauGraph()
        self._shift_checker = ShiftingEquivalenceChecker(formula)
        self._st_checker = StutteringEquivalenceChecker(formula)
        # self.depths: Dict[int, Set[Node]] = dict()

        self._node_hash: Dict[hash, Node] = dict()
        # self._node_lb_dict: Dict[Tuple[FrozenSet[Formula], int], Node] = dict()
        self._shift_resets: Dict[Jump, Tuple[int, int]] = dict()

    def expand(self):
        while True:
            yield self._expand()

    def _expand(self):
        self._prepare()

        prev_n = len(self.graph.nodes)
        if self._depth == 1:
            self._expand_init_nodes()
        else:
            self._expand_nodes()

        cur_n = len(self.graph.nodes)
        print("depth#{}, nodes#{}, nodesAcc#{}".format(self._depth, cur_n - prev_n, cur_n))

    def _prepare(self):
        self._depth += 1

    def _reset(self):
        self._depth = 0
        self._labels = set()
        self._shift_resets = dict()

    def _expand_init_nodes(self):
        nodes = list()
        lb_s = init(self._formula, self._threshold)
        for lb in lb_s:
            # ignore top formula
            lb.cur.discard(self._formula)
            node = Node(lb, 1)
            node.set_as_initial()
            nodes.append(node)

            if _is_final_label(lb):
                node.set_as_final()

        for node in nodes:
            self._add_fresh_node(node)

    def _expand_nodes(self):
        # bfs expand
        cur_node = self._next_nodes.copy()
        self._next_nodes.clear()

        for node in cur_node:
            self._expand_node(node)

    def _expand_node(self, node: 'Node'):
        nodes = set(node.expand(self._formula, self._threshold))
        # nodes = self._reduce_equivalent(*nodes)
        self._stuttering(node, nodes)
        self._reduce_shifting(node, nodes)

        # make new nodes for the rests
        for n in nodes:
            self._add_fresh_node(n)

            jp = Jump(node, n)
            connect(jp)

    @classmethod
    def _reduce_equivalent(cls, *nodes) -> Set['Node']:
        canonicalize: Dict[hash, Node] = dict()
        for n in nodes:
            assert isinstance(n, Node)
            if n.get_hash() in canonicalize:
                f_n = canonicalize[n.get_hash()]
                cls._merge_node(n, f_n)
            else:
                canonicalize[n.get_hash()] = n

        return {canonicalize[h] for h in canonicalize}

    @classmethod
    def _merge_node(cls, node1: 'Node', node2: 'Node'):
        # merge node1 to node2
        node2.labels.update(node1.labels)
        in_edges, out_edges = node1.get_in_edges(), node1.get_out_edges()

        for jp in in_edges:
            new_jp = copy_jump(jp)
            new_jp.trg = node2
            connect(new_jp)
            disconnect(jp)

        for jp in out_edges:
            new_jp = copy_jump(jp)
            new_jp.src = node2
            connect(new_jp)
            disconnect(jp)

    def _stuttering(self, node: 'Node', nodes: Set['Node']):
        redundancies: Set[Node] = set()
        for n in nodes:
            if self._st_checker.equivalent(node.get_label(), n.get_label()):
                redundancies.add(n)
        nodes.difference_update(redundancies)

    def _reduce_shifting(self, node: 'Node', nodes: Set['Node']):
        redundancies: Set[Node] = set()
        # find the matching case and remove redundancies
        # and add reset edge
        for n in nodes:
            found, f_n, shifting = self._find_shift_node_by_lb(n.get_label())
            if found:
                # redundant
                redundancies.add(n)

                # make reset edge
                jp = Jump(node, f_n)
                connect(jp)

                self._shift_resets[jp] = (n.depth, shifting)

        nodes.difference_update(redundancies)

    def _find_shift_node_by_lb(self, label: Set[Formula]) -> Tuple[bool, Optional['Node'], int]:
        for node in self.graph.nodes:
            if node.depth >= self._depth:
                continue

            if self._shift_checker.equivalent(node.get_label(), label, depth1=node.depth, depth2=self._depth):
                return True, node, self._shift_checker.get_shifting()
        return False, None, -1

    def _add_fresh_node(self, node: 'Node'):
        found, f_node = self._find_equiv_node(node)
        if not found:
            self.graph.nodes.add(node)
            self._next_nodes.add(node)
            self._node_hash[node.get_hash()] = node
        else:
            print(node)
            print("to")
            print(f_node)
            print("-==-=====")
            self._merge_node(node, f_node)

    def _find_equiv_node(self, node: 'Node') -> Tuple[bool, Optional['Node']]:
        node_hash = node.get_hash()
        if node_hash in self._node_hash:
            return True, self._node_hash[node_hash]
        else:
            return False, None

    def add_shift_resets(self):
        max_depth = self.graph.get_max_depth()
        for jp in self._shift_resets:
            depth, shifting = self._shift_resets[jp]
            print("shifting {}".format(shifting))
            jp.add_shift_reset(depth, shifting, max_depth)

    def remove_unreachable(self):
        reach = _find_reachable(self.graph)
        un_reach = self.graph.nodes.difference(reach)

        for node in un_reach:
            self.graph.remove_node(node)


class TableauGraph(Graph['Node', 'Jump']):
    def __init__(self):
        Graph.__init__(self)
        self.nodes: Set[Node] = set()

    def remove_node(self, node: 'Node'):
        self.nodes.discard(node)

        pred = node.get_in_edges()
        succ = node.get_out_edges()

        for e in pred:
            disconnect(e)

        for e in succ:
            disconnect(e)

    def get_max_depth(self) -> int:
        return max(map(lambda n: n.depth, self.nodes))

    def __repr__(self):
        return "\n".join([str(node) for node in self.nodes])


class Node(Vertex['Node', 'Jump']):
    def __init__(self, label: Label, depth: int):
        Vertex.__init__(self)

        non_inter, inter = split_label(label)

        self.non_intermediate: FrozenSet[Formula] = frozenset(non_inter)
        self.intermediate: FrozenSet[Formula] = frozenset(inter)

        self.labels: Set[Label] = {label}
        # self._hash = hash((self.non_intermediate, self.intermediate, depth))

        self._depth = depth
        self._is_final = False
        self._is_initial = False

    def expand(self, top_formula: Formula, threshold: float) -> List['Node']:
        new_nodes = list()
        for lb in self.labels:
            new_nodes.extend(self._expand(lb, top_formula, threshold))
        return new_nodes

    def _expand(self, label: Label, top_formula: Formula, threshold: float) -> List['Node']:
        new_nodes = list()
        lb_s = expand(label, self._depth, threshold)

        for lb in lb_s:
            # ignore top formula
            lb.cur.discard(top_formula)
            node = Node(lb, self._depth + 1)
            new_nodes.append(node)

            if _is_final_label(lb):
                node.set_as_final()

        return new_nodes

    def get_label(self) -> Set[Formula]:
        return set(self.non_intermediate.union(self.intermediate))

    # def __hash__(self):
    #     return self._hash

    # def __eq__(self, other):
    #     return hash(self) == hash(other)

    def __repr__(self):
        ap_str_list = list()
        for b in self.non_intermediate:
            ap_str_list.append(indented_str(str(b), 6))

        non_str_list = list()
        for b in self.intermediate:
            non_str_list.append(indented_str(str(b), 6))

        id_info = indented_str("id: {}".format(self.node_id), 4)
        depth_info = indented_str("depth: {}".format(self._depth), 4)
        ap_info = indented_str("ap:\n{}".format("\n".join(ap_str_list)), 4)
        non_info = indented_str("non ap:\n{}".format("\n".join(non_str_list)), 4)

        pred: Set[Node] = self.get_in_vertices()
        succ: Set[Node] = self.get_out_vertices()

        pred_body = "\n".join([indented_str(str(p.node_id), 6) for p in pred])
        pred_info = indented_str("pred:\n{}".format(pred_body), 4)

        succ_body = "\n".join([indented_str(str(s.node_id), 6) for s in succ])
        succ_info = indented_str("succ:\n{}".format(succ_body), 4)

        return "( Node\n{}\n)".format("\n".join([id_info, depth_info, ap_info, non_info, pred_info, succ_info]))

    @property
    def depth(self):
        return self._depth

    @property
    def node_id(self):
        return self.get_hash()

    def get_hash(self):
        return hash((self.non_intermediate, self.intermediate, self.depth))

    def set_as_final(self):
        self._is_final = True

    def is_final(self):
        return self._is_final

    def set_as_initial(self):
        self._is_initial = True

    def is_initial(self):
        return self._is_initial


class Jump(Edge[Node]):
    def __init__(self, src: Node, trg: Node):
        Edge.__init__(self, src, trg)
        self.reset: Set[Tuple[Real, Formula]] = set()

    def add_reset(self, *resets):
        for v, f in resets:
            self.reset.add((v, f))

    def add_shift_reset(self, depth: int, shift: int, max_depth: int):
        self.add_reset(*shift_reset(depth, shift, max_depth))

    def __repr__(self):
        reset_body = "\n".join([indented_str("{} := {}".format(v, f), 6) for v, f in self.reset])
        reset_str = indented_str("reset:\n{}".format(reset_body), 4)

        jp_body = indented_str("{} -> {}".format(self.src.node_id, self.trg.node_id), 4)

        return "( jump \n{}\n{}\n  )".format(reset_str, jp_body)


def get_node_jumps(graph: TableauGraph) -> Set[Jump]:
    jp_s: Set[Jump] = set()
    for node in graph.nodes:
        jp_s.update(node.get_out_edges())

    return jp_s


def copy_jump(jp: Jump) -> Jump:
    n_jp = Jump(jp.src, jp.trg)
    n_jp.add_reset(*jp.reset)
    return n_jp


def _is_final_label(label: Label):
    return len(label.nxt) == 0


def _is_initial_node(node: Node):
    return node.depth == 1


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


def _tau_index(tau: Real) -> int:
    return int(tau.id.split("_")[1])


def _shift_tau(tau: Real, shift: int):
    t_index = _tau_index(tau)
    assert t_index - shift >= 0
    return Real("tau_{}".format(t_index - shift))


def shift_reset(src: int, shift: int, max_depth: int) -> Set[Tuple[Real, Real]]:
    resets: Set[Tuple[Real, Real]] = set()

    interval = symbolic_interval(src)
    _, e_tau = inf(interval), sup(interval)

    glk = global_clk()

    t_vs_all = time_variables(max_depth)
    t_vs = time_variables(src)

    # remove global clk
    t_vs_all.discard(glk)
    t_vs.discard(glk)

    used = set()
    for t_v in t_vs:
        t_index = _tau_index(t_v)
        if t_index - shift < 0:
            continue

        shifted_tau = _shift_tau(t_v, shift)
        used.add(shifted_tau)

        if variable_equal(t_v, e_tau):
            resets.add((shifted_tau, glk))
        else:
            resets.add((shifted_tau, t_v))

    l_vs = t_vs_all.difference(used)
    resets = resets.union({(t_v, t_v) for t_v in l_vs})

    return resets
