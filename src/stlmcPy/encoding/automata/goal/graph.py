from itertools import product
from typing import Set, Dict, FrozenSet, Tuple

from .aux import Label, Labels, split_label
from ....constraints.constraints import Real, Expr
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

        self.non_intermediate: Labels = frozenset()
        self.intermediate: Labels = frozenset()

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


# def composition(graph1: Graph, graph2: Graph):
#     graph = Graph()
#
#     candidate_nodes: Set[Tuple[Node, Node]] = set(product(graph1.nodes, graph2.nodes))
#     node_dict: Dict[Tuple[Node, Node], Node] = dict()
#
#     for node1, node2 in candidate_nodes:
#         node = _compose_node(node1, node2)
#         graph.add_node(node)
#
#     for node1, node2 in candidate_nodes:
#         node_src = node_dict[(node1, node2)]
#
#         for succ in node1.succ:
#             trg_nodes = _find_composed_nodes(succ, node_dict)
#
#             for trg_node in trg_nodes:
#                 connect(node_src, trg_node)
#
#         for succ in node2.succ:
#             trg_nodes = _find_composed_nodes(succ, node_dict)
#
#             for trg_node in trg_nodes:
#                 connect(node_src, trg_node)
#
#     return graph
#
#
# def _compose_node(node1: Node, node2: Node) -> Node:
#     labels_non_intermediate = node1.non_intermediate.union(node2.non_intermediate)
#     labels_intermediate = node1.intermediate.union(node2.intermediate)
#
#     labels = frozenset(labels_non_intermediate.union(labels_intermediate))
#     node = Node(hash(labels), -1)
#     node.non_intermediate, node.intermediate = split_label(labels)
#
#     for v in node1.dynamics:
#         node.dynamics[v] = node1.dynamics[v]
#
#     for v in node2.dynamics:
#         node.dynamics[v] = node2.dynamics[v]
#
#     if node1.is_initial() and node2.is_initial():
#         node.set_as_initial()
#
#     if node1.is_final() and node2.is_final():
#         node.set_as_final()
#
#     return node
#
#
# def _find_composed_nodes(node: Node, node_dict: Dict[Tuple[Node, Node], Node]) -> Set[Node]:
#     found: Set[Node] = set()
#     for pair in node_dict:
#         if node in pair:
#             found.add(node_dict[pair])
#
#     return found
