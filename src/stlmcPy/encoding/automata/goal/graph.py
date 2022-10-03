from itertools import product
from typing import Set, Dict, FrozenSet, Tuple

# from .aux import Label, Labels, split_label
from ....constraints.constraints import Real, Expr, Formula
from ....util.printer import indented_str


class Graph:
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

        node_pred = node.pred.copy()
        for pred in node_pred:
            disconnect(pred, node)

        node_succ = node.succ.copy()
        for succ in node_succ:
            disconnect(node, succ)

    def get_max_depth(self) -> int:
        if len(self.depths) == 0:
            return -1
        return max(self.depths.keys())

    def get_nodes_at(self, depth: int) -> Set['Node']:
        assert depth in self.depths
        return self.depths[depth].copy()

    def __repr__(self):
        return "\n".join([str(node) for node in self.nodes])


class Node:
    def __init__(self, node_id: hash, depth: int):
        self.pred: Set[Node] = set()
        self.succ: Set[Node] = set()

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

        pred_body = "\n".join([indented_str(str(p.node_id), 6) for p in self.pred])
        pred_info = indented_str("pred:\n{}".format(pred_body), 4)

        succ_body = "\n".join([indented_str(str(s.node_id), 6) for s in self.succ])
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


def connect(n1: Node, n2: Node):
    n1.succ.add(n2)
    n2.pred.add(n1)


def disconnect(n1: Node, n2: Node):
    n1.succ.discard(n2)
    n2.pred.discard(n1)

