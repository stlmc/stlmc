
class Interval:
    def __init__(self, leftend, left, rightend, right):
        self.leftend  = leftend
        self.left     = left
        self.rightend = rightend
        self.right    = right

    def __repr__(self):
        return ('[' if self.leftend else '(') + repr(self.left) + ',' + repr(self.right) + (']' if self.rightend else ')')

universeInterval = Interval(True, 0, False, float('inf'))
