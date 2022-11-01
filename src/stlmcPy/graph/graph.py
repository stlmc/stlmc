import abc
from typing import Set, Dict, Type, Tuple, TypeVar, Generic

V = TypeVar('V')
E = TypeVar('E')


class Graph(Generic[V, E]):
    pass


class Vertex(Generic[V, E]):
    def __init__(self):
        self.pred: Dict[V, Set[E]] = dict()
        self.succ: Dict[V, Set[E]] = dict()

    def get_out_vertices(self) -> Set[V]:
        return set(self.succ.keys())

    def get_in_vertices(self) -> Set[V]:
        return set(self.pred.keys())

    def get_out_edges(self) -> Set[E]:
        edges = set()
        for s_v in self.succ:
            for e in self.succ[s_v]:
                edges.add(e)

        return edges

    def get_in_edges(self) -> Set[E]:
        edges = set()
        for p_v in self.pred:
            for e in self.pred[p_v]:
                edges.add(e)

        return edges


class Edge(Generic[V]):
    def __init__(self, src: V, trg: V):
        self.src, self.trg = src, trg


def connect(edge: E):
    v1, v2 = edge.src, edge.trg

    _add_to_dict(v1.succ, v2, edge)
    _add_to_dict(v2.pred, v1, edge)

    return edge


def disconnect(edge: E):
    v1, v2 = edge.src, edge.trg

    assert v2 in v1.succ
    assert v1 in v2.pred

    v1.succ[v2].remove(edge)
    v2.pred[v1].remove(edge)

    if len(v1.succ[v2]) <= 0:
        del v1.succ[v2]

    if len(v2.pred[v1]) <= 0:
        del v2.pred[v1]

    del edge


def _add_to_dict(d: Dict[V, Set[E]], v: V, e: E):
    if v in d:
        d[v].add(e)
    else:
        d[v] = {e}
