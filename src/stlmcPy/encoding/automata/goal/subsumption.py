import abc

from .graph import *


class Subsumption:
    @abc.abstractmethod
    def calc_relation(self, graph: Graph):
        pass

    @abc.abstractmethod
    def reduce(self, graph: Graph):
        pass

    @abc.abstractmethod
    def get_relation(self):
        pass


class ForwardSubsumption(Subsumption):
    def __init__(self):
        self._relation: Dict[Node, Set[Node]] = dict()

    def calc_relation(self, graph: TableauGraph):
        self._calc_relation_until(graph.nodes)

    def reduce(self, graph: TableauGraph):
        nodes = graph.nodes.copy()

        waiting = nodes.copy()
        reduce: Dict[Node, Set[Node]] = dict()
        for node in nodes:
            reduce[node] = {node}

        while len(waiting) > 0:
            node = waiting.pop()

            remove = set()
            for n in waiting:
                if self._equivalent(node, n):
                    assert node in reduce
                    reduce[node].add(n)
                    remove.add(n)

            waiting.difference_update(remove)

        for representative in reduce:
            for node in reduce[representative]:
                if node != representative:
                    p_jp_s, s_jp_s = node.get_in_edges(), node.get_out_edges()

                    for p_jp in p_jp_s:
                        n_jp = copy_jump(p_jp)
                        n_jp.trg = representative
                        connect(n_jp)

                    for s_jp in s_jp_s:
                        n_jp = copy_jump(s_jp)
                        n_jp.src = representative
                        connect(n_jp)

                    graph.remove_node(node)

    def get_relation(self):
        return self._relation

    def _calc_relation_until(self, nodes: Set[Node]):
        pre_status: Dict[Node, Set[Node]] = self._relation.copy()
        while True:
            self._calc_relation(nodes)

            cur_status = self._relation
            if cur_status == pre_status:
                return

            pre_status = self._relation.copy()

    def _equivalent(self, node1: Node, node2: Node):
        assert node1 in self._relation and node2 in self._relation
        return node1 in self._relation[node2] and node2 in self._relation[node1]

    def _calc_relation(self, nodes: Set[Node]):
        for node in nodes:
            waiting = nodes.copy()
            while len(waiting) > 0:
                n = waiting.pop()
                if self._forward_relation(node, n):
                    self._add_to_relation(node, n)
                    if n in self._relation:
                        self._add_to_relation(node, *self._relation[n])
                        waiting.difference_update(self._relation[n])

    def _forward_relation(self, node1: Node, node2: Node):
        c1 = node1.non_intermediate.issuperset(node2.non_intermediate)
        c2 = not node1.is_initial() or node2.is_initial()

        if not c1 or not c2:
            return False

        for pred in node1.pred:
            # temporarily not forward relation
            # assert in self._relation
            if pred not in self._relation:
                return False

            if len(self._relation[pred].intersection(node2.pred)) <= 0:
                return False
        return True

    def _add_to_relation(self, node1: Node, *nodes):
        if node1 not in self._relation:
            self._relation[node1] = {node for node in nodes}
        else:
            for node in nodes:
                self._relation[node1].add(node)


class BackwardSubsumption(Subsumption):
    def __init__(self):
        self._relation: Dict[Node, Set[Node]] = dict()

    def calc_relation(self, graph: TableauGraph):
        self._calc_relation_until(graph.nodes)

    def reduce(self, graph: TableauGraph):
        nodes = graph.nodes.copy()

        waiting = nodes.copy()
        reduce: Dict[Node, Set[Node]] = dict()
        for node in nodes:
            reduce[node] = {node}

        while len(waiting) > 0:
            node = waiting.pop()

            remove = set()
            for n in waiting:
                if self._equivalent(node, n):
                    assert node in reduce
                    reduce[node].add(n)
                    remove.add(n)

            waiting.difference_update(remove)

        for representative in reduce:
            for node in reduce[representative]:
                if node != representative:
                    p_jp_s, s_jp_s = node.get_in_edges(), node.get_out_edges()

                    for p_jp in p_jp_s:
                        n_jp = copy_jump(p_jp)
                        n_jp.trg = representative
                        connect(n_jp)

                    for s_jp in s_jp_s:
                        n_jp = copy_jump(s_jp)
                        n_jp.src = representative
                        connect(n_jp)

                    graph.remove_node(node)

    def get_relation(self):
        return self._relation

    def _calc_relation_until(self, nodes: Set[Node]):
        pre_status: Dict[Node, Set[Node]] = self._relation.copy()
        while True:
            self._calc_relation(nodes)

            cur_status = self._relation
            if cur_status == pre_status:
                return

            pre_status = self._relation.copy()

    def _equivalent(self, node1: Node, node2: Node):
        assert node1 in self._relation and node2 in self._relation
        return node1 in self._relation[node2] and node2 in self._relation[node1]

    def _calc_relation(self, nodes: Set[Node]):
        for node in nodes:
            waiting = nodes.copy()
            while len(waiting) > 0:
                n = waiting.pop()
                if self._backward_relation(node, n):
                    self._add_to_relation(node, n)
                    if n in self._relation:
                        self._add_to_relation(node, *self._relation[n])
                        waiting.difference_update(self._relation[n])

    def _backward_relation(self, node1: Node, node2: Node):
        c1 = node1.non_intermediate.issuperset(node2.non_intermediate)
        c2 = not node1.is_final() or node2.is_final()

        if not c1 or not c2:
            return False

        for succ in node1.succ:
            if succ not in self._relation:
                return False

            if len(self._relation[succ].intersection(node2.succ)) <= 0:
                return False
        return True

    def _add_to_relation(self, node1: Node, *nodes):
        if node1 not in self._relation:
            self._relation[node1] = {node for node in nodes}
        else:
            for node in nodes:
                self._relation[node1].add(node)


class PathSubsumption:
    def __init__(self, forward_relation: Dict[Node, Set[Node]],
                 backward_relation: Dict[Node, Set[Node]]):
        self._forward_relation: Dict[Node, Set[Node]] = forward_relation
        self._backward_relation: Dict[Node, Set[Node]] = backward_relation

    def reduce(self, graph: TableauGraph):
        nodes = graph.nodes.copy()

        waiting = nodes.copy()
        reduce: Dict[Node, Set[Node]] = dict()
        for node in nodes:
            reduce[node] = {node}

        while len(waiting) > 0:
            node = waiting.pop()

            remove = set()
            for n in nodes:
                if self._subsume(n, node):
                    assert node in reduce
                    reduce[node].add(n)
                    remove.add(n)

            waiting.difference_update(remove)

        for representative in reduce:
            for node in reduce[representative]:
                if node != representative:
                    graph.remove_node(node)

    def _subsume(self, node1: Node, node2: Node):
        assert node1 in self._backward_relation
        assert node1 in self._forward_relation

        c1 = node2 in self._forward_relation[node1]
        c2 = node2 in self._backward_relation[node1]

        return c1 and c2
