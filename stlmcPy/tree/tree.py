class Tree:
    def __init__(self):
        pass


class Leaf(Tree):
    def __init__(self):
        super().__init__()


class NonLeaf(Tree):
    def __init__(self, children):
        super().__init__()
        self.children = children
