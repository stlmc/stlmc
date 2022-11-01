from itertools import product
from typing import Set, Dict, FrozenSet, Tuple

# from .aux import Label, Labels, split_label
from ....constraints.constraints import Real, Expr, Formula
from ....graph.graph import *
from ....util.printer import indented_str, p_string


class TableauGraph(Graph['Node', 'Jump']):
    def __init__(self):
        self.nodes: Set[Node] = set()
        self.depths: Dict[int, Set[Node]] = dict()

    def add_node(self, node: 'Node'):
        node_depth = node.depth
        if node_depth in self.depths:
            self.depths[node_depth].add(node)
        else:
            self.depths[node_depth] = {node}
        self.nodes.add(node)

    def remove_node(self, node: 'Node'):
        self.nodes.discard(node)
        node_depth = node.depth
        if node_depth in self.depths:
            self.depths[node_depth].discard(node)

        pred = node.get_in_edges()
        succ = node.get_out_edges()

        for e in pred:
            disconnect(e)

        for e in succ:
            disconnect(e)

    def remove_jump(self, jp: 'Jump'):
        jp_s = get_node_jumps(self)
        assert jp in jp_s

        src, trg = jp.src, jp.trg
        src.succ[trg].remove(jp)

        if len(src.succ[trg]) <= 0:
            del src.succ[trg]

        trg.pred[src].remove(jp)

        if len(trg.pred[src]) <= 0:
            del trg.pred[src]

        del jp

    def get_max_depth(self) -> int:
        if len(self.depths) == 0:
            return -1
        return max(self.depths.keys())

    def get_nodes_at(self, depth: int) -> Set['Node']:
        assert depth in self.depths
        return self.depths[depth].copy()

    def __repr__(self):
        return "\n".join([str(node) for node in self.nodes])


class Node(Vertex['Node', 'Jump']):
    def __init__(self, node_id: hash, depth: int):
        Vertex.__init__(self)

        self.non_intermediate: Set[Formula] = set()
        self.intermediate: Set[Formula] = set()

        self._node_id = node_id
        self._depth = depth
        self._is_final = False
        self._is_initial = False

    def __repr__(self):
        ap_str_list = list()
        for b in self.non_intermediate:
            ap_str_list.append(indented_str(str(b), 6))

        non_str_list = list()
        for b in self.intermediate:
            non_str_list.append(indented_str(str(b), 6))

        id_info = indented_str("id: {}".format(self._node_id), 4)
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
        return self._node_id

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

