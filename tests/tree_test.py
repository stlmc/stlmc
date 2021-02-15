import unittest

from stlmcPy.tree.tree import Leaf, NonLeaf
from stlmcPy.tree.operations import size_of_tree


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
