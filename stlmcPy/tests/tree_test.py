import unittest

from stlmcPy.tree.tree import Leaf, NonLeaf
from stlmcPy.tree.operations import size_of_tree, new_size_of_tree


def gen_binary_tree(depth: int):
    width = 2 ** (depth - 1)
    queue = list()
    new_queue = list()
    root = None
    for i in range(width):
        queue.append(Leaf())
    while len(queue) > 0 or len(new_queue) > 0:
        if len(queue) == 0:
            queue = new_queue.copy()
            new_queue.clear()
            continue
        if len(queue) == 1:
            root = queue.pop(0)
            break

        left = queue.pop(0)
        right = queue.pop(0)
        parent = NonLeaf([left, right])
        new_queue.append(parent)

    return root


class TreeTestCase(unittest.TestCase):

    def test_default_children_size(self):
        children = list()
        child_size = 5
        for i in range(child_size):
            children.append(Leaf())
        tree = NonLeaf(children)
        self.assertEqual(size_of_tree(tree), 1,
                         'incorrect children size')

    def test_non_leaf_size(self):
        children = list()
        children.append(Leaf())

        sub_children = list()
        sub_children.append(Leaf())
        sub_children.append(Leaf())

        sub_tree = NonLeaf(sub_children)

        children.append(Leaf())
        children.append(sub_tree)

        tree = NonLeaf(children)

        self.assertEqual(size_of_tree(tree), 2,
                         'incorrect children size')

    def test_gen_tree(self):
        root1 = gen_binary_tree(4)
        root2 = gen_binary_tree(5)
        self.assertEqual(new_size_of_tree(root1), 15,
                         'incorrect children size')

        self.assertEqual(new_size_of_tree(root2), 31,
                         'incorrect children size')