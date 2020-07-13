from .base import *
from stlmcPy.constraints.node import Type


class Formula:
    def getType(self):
        return Type.Bool
        # return Type.Bool


class NotFormula(Unary, Formula):
    op = '~'

class ConstantFormula(Atomic, Formula):
    def __init__(self, value):
        super().__init__(True if value == 'true' else False)
    def getValue(self):
        return self.id

class PropositionFormula(Atomic, Formula):
    pass


class AndFormula(Multiary, Formula):
    op = 'and'

class OrFormula(Multiary, Formula):
    op = 'or'


class ImpliesFormula(Binary, Formula):
    op = '->'

class UnaryTemporalFormula(Unary, Formula):
    def __init__(self, ltime, gtime, child):
        super().__init__(child)
        self.ltime = ltime
        self.gtime = gtime
    def __str__(self):
        return '(' + self.op+ '_' + str(self.ltime) + '^' + str(self.gtime) + ' ' + str(self.child) + ')'
    def temporalHeight(self):
        return 1 + self.child.temporalHeight()

class GloballyFormula(UnaryTemporalFormula):
    op = '[]'


class FinallyFormula(UnaryTemporalFormula):
    op = '<>'


class BinaryTemporalFormula(Binary, Formula):
    def __init__(self, ltime, gtime, left, right):
        super().__init__(left, right)
        self.ltime = ltime
        self.gtime = gtime
    def __str__(self):
        return '(' + str(self.left) + ' ' + self.op + '_' + str(self.ltime) + '^' + str(self.gtime) + ' ' + str(self.right) + ')'
    def temporalHeight(self):
        return 1 + max(self.left.temporalHeight(), self.right.temporalHeight())

class UntilFormula(BinaryTemporalFormula):
    op = 'U'


class ReleaseFormula(BinaryTemporalFormula):
    op = 'R'


def numTemp(tree):
    stack = [tree]
    fs = 0
    while (stack):
        curr = stack.pop()
        if isinstance(curr,Atomic):
            pass
        elif isinstance(curr,UnaryTemporalFormula):
            fs = fs + 1
            stack.append(curr.child)
        elif isinstance(curr,BinaryTemporalFormula):
            fs = fs + 1
            stack.append(curr.left)
            stack.append(curr.right)
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
