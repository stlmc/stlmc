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
        self.assertEqual(size_of_tree(tree), child_size + 1,
                         'incorrect children size')
