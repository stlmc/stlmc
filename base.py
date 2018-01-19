class Atomic:
    def __init__(self, id):
        self.id = id
    def __hash__(self):
        return hash(self.id)
    def __repr__(self):
        return str(self.id)
    def size(self):
        return 1


class Unary:
    def __init__(self, child):
        self.child = child
    def __str__(self):
        return '(' + self.op + ' ' + str(self.child) + ')'
    def size(self):
        return self.child.size() + 1


class Binary:
    def __init__(self, left, right):
        self.left  = left
        self.right = right
    def __str__(self):
        return '(' + str(self.left) + ' ' + self.op+ ' ' + str(self.right) + ')'
    def size(self):
        return self.left.size() + self.right.size() + 1
