from functools import singledispatch
from .tree import *
from ..exception.exception import NotSupportedError


def size_of_tree(tree: Tree):
    if tree is None:
        return 0
    size = 0
    waiting_queue = set()
    waiting_queue.add(tree)
    while len(waiting_queue) > 0:
        t = waiting_queue.pop()
        if isinstance(t, Leaf):
            # print("Leaf , {}".format(id(t)))
            size += 1
        elif isinstance(t, NonLeaf):
            # print("NonLeaf , {}".format(id(t)))
            size += 1
            for child in t.children:
                waiting_queue.add(child)
        else:
            raise NotSupportedError("cannot calculate size of {}".format(t))
    return size
