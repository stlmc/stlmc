
def genId(initial, gid = 'v'):
    counter = initial
    while True:
        yield gid + str(counter)
        counter += 1


class Interval:
    def __init__(self, leftend, left, rightend, right):
        self.leftend  = leftend
        self.left     = left
        self.rightend = rightend
        self.right    = right

    def __repr__(self):
        return ('[' if self.leftend else '(') + repr(self.left) + ',' + repr(self.right) + (']' if self.rightend else ')')


universeInterval = Interval(True, 0.0, False, float('inf'))


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


class Multiary:
    def __init__(self, children):
        self.children = []
        for c in children:
            if isinstance(c, self.__class__):
                self.children.extend(c.children)
            else:
                self.children.append(c)
    def __str__(self):
        return '(' + (' ' + self.op + ' ').join([str(c) for c in self.children]) + ')'
    def size(self):
        return sum([c.size() for c in self.children]) + 1

