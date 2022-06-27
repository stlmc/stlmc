from ..exception.exception import NotSupportedError
from .tree import *


def size_of_tree(tree: Tree):
    if tree is None:
        return 0
    size = 0
    count = 0
    waiting_queue = set()
    waiting_queue.add((count, tree))
    while len(waiting_queue) > 0:
        count = count + 1
        _, t = waiting_queue.pop()
        if isinstance(t, Leaf):
            size += 1
        elif isinstance(t, NonLeaf):
            size += 1
            for child in t.children:
                waiting_queue.add((count, child))
        else:
            raise NotSupportedError("cannot calculate size of {}".format(t))
    return size


def elements_of_tree(tree: Tree) -> set:
    children = set()
    if tree is None:
        return children
    count = 0
    waiting_queue = set()
    waiting_queue.add((count, tree))
    while len(waiting_queue) > 0:
        count = count + 1
        _, t = waiting_queue.pop()
        if isinstance(t, Leaf):
            children.add(t)
        elif isinstance(t, NonLeaf):
            for child in t.children:
                waiting_queue.add((count, child))
        else:
            continue
    return children
