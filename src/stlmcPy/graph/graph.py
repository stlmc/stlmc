import abc
from typing import Set, Dict, Type, Tuple, TypeVar, Generic

V = TypeVar('V')
E = TypeVar('E')


class Graph(Generic[V, E]):
    def __init__(self):
        self.vertices: Set[V] = set()
        self._next: Dict[V, Dict[V, Set[E]]] = dict()
        self._pred: Dict[V, Dict[V, Set[E]]] = dict()

    def add_vertex(self, vertex: V):
        self.vertices.add(vertex)

    def remove_vertex(self, vertex: V):
        if vertex not in self.vertices:
            return

        to_be_removed: Set[E] = set()
        to_be_removed.update(self.get_next_edges(vertex))
        to_be_removed.update(self.get_pred_edges(vertex))

        for e in to_be_removed:
            self.remove_edge(e)

        self.vertices.remove(vertex)

    def add_edge(self, edge: E):
        v1, v2 = edge.get_src(), edge.get_trg()

        if v1 not in self.vertices or v2 not in self.vertices:
            raise Exception("src or trg does not exist")

        self._add_to_dict(self._next, v1, v2, edge)
        self._add_to_dict(self._pred, v2, v1, edge)

    def remove_edge(self, edge: E):
        v1, v2 = edge.get_src(), edge.get_trg()

        if v1 not in self.vertices or v2 not in self.vertices:
            raise Exception("src or trg does not exist")

        self._remove_from_dict(self._next, v1, v2, edge)
        self._remove_from_dict(self._pred, v2, v1, edge)

    def get_next_vertices(self, vertex: V) -> Set[V]:
        if vertex not in self._next:
            return set()
        return set(self._next[vertex].keys())

    def get_pred_vertices(self, vertex: V) -> Set[V]:
        if vertex not in self._pred:
            return set()
        return set(self._pred[vertex].keys())

    def get_next_edges(self, vertex: V) -> Set[E]:
        if vertex not in self._next:
            return set()

        edges, n_d = set(), self._next[vertex]
        for n_v in n_d:
            edges.update(n_d[n_v])
        return edges

    def get_pred_edges(self, vertex: V) -> Set[E]:
        if vertex not in self._pred:
            return set()

        edges, p_d = set(), self._pred[vertex]
        for p_v in p_d:
            edges.update(p_d[p_v])
        return edges

    @classmethod
    def _add_to_dict(cls, d: Dict[V, Dict[V, Set[E]]], v1: V, v2: V, e: E):
        if v1 in d:
            e_d = d[v1]
            if v2 in e_d:
                e_d[v2].add(e)
            else:
                e_d[v2] = {e}
        else:
            e_d: Dict[V, Set[E]] = dict()
            e_d[v2] = {e}
            d[v1] = e_d

    @classmethod
    def _remove_from_dict(cls, d: Dict[V, Dict[V, Set[E]]], v1: V, v2: V, e: E):
        if v1 in d:
            d_n = d[v1]
            if v2 in d_n:
                assert e in d_n[v2]
                d_n[v2].remove(e)
                del e

                if len(d_n[v2]) <= 0:
                    del d_n[v2]


class Edge(Generic[V]):
    @abc.abstractmethod
    def get_src(self) -> V:
        pass

    @abc.abstractmethod
    def get_trg(self) -> V:
        pass
