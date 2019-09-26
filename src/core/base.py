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
    def height(self):
        return 0


class Unary:
    def __init__(self, child):
        self.child = child
    def __str__(self):
        return '(' + self.op + ' ' + str(self.child) + ')'
    def height(self):
        return 1 + self.child.height()


class Binary:
    def __init__(self, left, right):
        self.left  = left
        self.right = right
    def __str__(self):
        return '(' + str(self.left) + ' ' + self.op+ ' ' + str(self.right) + ')'
    def height(self):
        return 1 + max(self.left.height(),self.right.height())


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
    def height(self):
        return 1 + max([c.height() for c in self.children])


def size(tree):
    stack = [tree]
    fs = 0
    while (stack):
        curr = stack.pop()
        fs += 1
        if isinstance(curr,Atomic):
            pass
        elif isinstance(curr,Unary):
            stack.append(curr.child)
        elif isinstance(curr,Binary):
            stack.append(curr.left)
            stack.append(curr.right)
        elif isinstance(curr,Multiary):
            stack.extend(curr.children)
        else:
            raise NotImplementedError('Something wrong')
    return fs

