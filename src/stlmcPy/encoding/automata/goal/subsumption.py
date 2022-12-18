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
        # add self subsumption because of loop
        for node in graph.get_nodes():
            self._relation[node] = {node}
        self._calc_relation_until(graph)

    def reduce(self, graph: TableauGraph):
        nodes = graph.get_nodes().copy()

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
                    p_jp_s, s_jp_s = graph.get_pred_edges(node), graph.get_next_edges(node)

                    for p_jp in p_jp_s:
                        n_jp = Jump(p_jp.get_src(), representative, p_jp.get_ap())
                        graph.add_jump(n_jp)

                    for s_jp in s_jp_s:
                        n_jp = Jump(representative, s_jp.get_trg(), s_jp.get_ap())
                        graph.add_jump(n_jp)

                    graph.remove_node(node)

    def get_relation(self):
        return self._relation

    def _calc_relation_until(self, graph: TableauGraph):
        pre_status: Dict[Node, Set[Node]] = self._relation.copy()
        while True:
            self._calc_relation(graph)

            cur_status = self._relation
            if cur_status == pre_status:
                return

            pre_status = self._relation.copy()

    def _equivalent(self, node1: Node, node2: Node):
        assert node1 in self._relation and node2 in self._relation
        return node1 in self._relation[node2] and node2 in self._relation[node1]

    def _calc_relation(self, graph: TableauGraph):
        explored = set()
        waiting_queue = set(filter(lambda x: x.is_initial(), graph.get_nodes()))
        next_queue = self._calc_next_queue(waiting_queue, graph)

        while True:
            # update queue
            if len(waiting_queue) <= 0:
                # if previously calculated queue was empty
                if len(next_queue) <= 0:
                    break

                waiting_queue = next_queue
                next_queue = self._calc_next_queue(waiting_queue, graph)
                next_queue.difference_update(explored)

            node = waiting_queue.pop()
            explored.add(node)

            waiting = graph.get_nodes().copy()
            while len(waiting) > 0:
                n = waiting.pop()
                if self._forward_relation(node, n, graph):
                    self._add_to_relation(node, n)
                    if n in self._relation:
                        self._add_to_relation(node, *self._relation[n])
                        waiting.difference_update(self._relation[n])

    @classmethod
    def _calc_next_queue(cls, nodes: Set[Node], graph: TableauGraph) -> Set[Node]:
        next_queue = set()

        for node in nodes:
            nxt_nodes = graph.get_next_vertices(node)
            next_queue.update(nxt_nodes)

        return next_queue

    def _forward_relation(self, node1: Node, node2: Node, graph: TableauGraph):
        # node1 is subsumed to node2
        non_intermediate = [set(filter(lambda x: isinstance(x, Proposition), node1.goals)),
                            set(filter(lambda x: isinstance(x, Proposition), node2.goals))]
        c1 = non_intermediate[0].issuperset(non_intermediate[1])
        c2 = not node1.is_initial() or node2.is_initial()

        if not c1 or not c2:
            return False

        jp1_s = graph.get_pred_edges(node1)
        while len(jp1_s) > 0:
            jp1 = jp1_s.pop()

            found = False
            for jp2 in graph.get_pred_edges(node2):
                if self._forward_pair_relation(jp1, node1, jp2, node2):
                    found = True
                    break
            # if any found
            if found:
                continue
            else:
                # fail to find subsumption
                return False
        return True

    def _forward_pair_relation(self, jump1: Jump, node1: Node, jump2: Jump, node2: Node):
        assert jump1.get_trg() == node1 and jump2.get_trg() == node2

        c = jump1.get_ap().issuperset(jump2.get_ap())
        if not c:
            return False

        n1_pred, n2_pred = jump1.get_src(), jump2.get_src()
        if n2_pred not in self._relation[n1_pred]:
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
        # add self subsumption because of loop
        for node in graph.get_nodes():
            self._relation[node] = {node}
        self._calc_relation_until(graph)

    def reduce(self, graph: TableauGraph):
        nodes = graph.get_nodes().copy()

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
                    p_jp_s, s_jp_s = graph.get_pred_edges(node), graph.get_next_edges(node)

                    for p_jp in p_jp_s:
                        n_jp = Jump(p_jp.get_src(), representative, p_jp.get_ap())
                        graph.add_jump(n_jp)

                    for s_jp in s_jp_s:
                        n_jp = Jump(representative, s_jp.get_trg(), s_jp.get_ap())
                        graph.add_jump(n_jp)

                    graph.remove_node(node)

    def get_relation(self):
        return self._relation

    def _calc_relation_until(self, graph: TableauGraph):
        pre_status: Dict[Node, Set[Node]] = self._relation.copy()
        while True:
            self._calc_relation(graph)

            cur_status = self._relation
            if cur_status == pre_status:
                return

            pre_status = self._relation.copy()

    def _equivalent(self, node1: Node, node2: Node):
        assert node1 in self._relation and node2 in self._relation
        return node1 in self._relation[node2] and node2 in self._relation[node1]

    def _calc_relation(self, graph: TableauGraph):
        explored = set()
        waiting_queue = set(filter(lambda x: x.is_final(), graph.get_nodes()))
        next_queue = self._calc_prev_queue(waiting_queue, graph)

        while True:
            # update queue
            if len(waiting_queue) <= 0:
                # if previously calculated queue was empty
                if len(next_queue) <= 0:
                    break

                waiting_queue = next_queue
                next_queue = self._calc_prev_queue(waiting_queue, graph)
                next_queue.difference_update(explored)

            node = waiting_queue.pop()
            explored.add(node)

            waiting = graph.get_nodes().copy()
            while len(waiting) > 0:
                n = waiting.pop()
                if self._backward_relation(node, n, graph):
                    self._add_to_relation(node, n)
                    if n in self._relation:
                        self._add_to_relation(node, *self._relation[n])
                        waiting.difference_update(self._relation[n])

    @classmethod
    def _calc_prev_queue(cls, nodes: Set[Node], graph: TableauGraph) -> Set[Node]:
        prev_queue = set()

        for node in nodes:
            prev_nodes = graph.get_pred_vertices(node)
            prev_queue.update(prev_nodes)

        return prev_queue

    def _backward_relation(self, node1: Node, node2: Node, graph: TableauGraph):
        # node1 is subsumed to node2
        non_intermediate = [set(filter(lambda x: isinstance(x, Proposition), node1.goals)),
                            set(filter(lambda x: isinstance(x, Proposition), node2.goals))]
        c1 = non_intermediate[0].issuperset(non_intermediate[1])
        c2 = not node1.is_final() or node2.is_final()
        if not c1 or not c2:
            return False

        jp1_s = graph.get_next_edges(node1)
        while len(jp1_s) > 0:
            jp1 = jp1_s.pop()

            found = False
            for jp2 in graph.get_next_edges(node2):
                if self._backward_pair_relation(jp1, node1, jp2, node2):
                    found = True
                    break
            # if any found
            if found:
                continue
            else:
                # fail to find subsumption
                return False
        return True

    def _backward_pair_relation(self, jump1: Jump, node1: Node, jump2: Jump, node2: Node):
        assert jump1.get_src() == node1 and jump2.get_src() == node2

        # node1 is subsumed to node2
        c = jump1.get_ap().issuperset(jump2.get_ap())
        if not c:
            return False

        n1_succ, n2_succ = jump1.get_trg(), jump2.get_trg()
        if n2_succ not in self._relation[n1_succ]:
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
        nodes = graph.get_nodes().copy()

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
