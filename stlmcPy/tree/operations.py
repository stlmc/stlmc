from functools import singledispatch
from .tree import *


@singledispatch
def size_of_tree(tree: Tree):
    return 0


@size_of_tree.register(NonLeaf)
def _(tree: NonLeaf):
    return 1 + sum([size_of_tree(c) for c in tree.children])
