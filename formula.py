
from base import *

class Formula:
    def __invert__(self):
        return NotFormula(self)
    def __and__(self, other):
        return AndFormula(self, other)
    def __or__(self, other):
        return OrFormula(self, other)
    def __rshift__(self, other):
        return ImpliesFormula(self, other)


class NotFormula(Formula, Unary):
    op = '~'


class ConstantFormula(Formula, Atomic):
    def __init__(self, value):
        super().__init__(True if value == 'true' else False)


class PropositionFormula(Formula, Atomic):
    pass


class BinaryFormula(Formula, Binary):
    pass


class AndFormula(BinaryFormula):
    op = '/\\'


class OrFormula(BinaryFormula):
    op = '\\/'


class ImpliesFormula(BinaryFormula):
    op = '->'


class UnaryTemporalFormula(Formula,Unary):
    def __init__(self, ltime, gtime, child):
        super().__init__(child)
        self.ltime = ltime
        self.gtime = gtime
    def __str__(self):
        return '(' + self.op+ '_' + str(self.ltime) + '^' + str(self.gtime) + ' ' + str(self.child) + ')'


class GloballyFormula(UnaryTemporalFormula):
    op = '[]'


class FinallyFormula(UnaryTemporalFormula):
    op = '<>'


class BinaryTemporalFormula(Formula,Binary):
    def __init__(self, ltime, gtime, left, right):
        super().__init__(left, right)
        self.ltime = ltime
        self.gtime = gtime
    def __str__(self):
        return '(' + str(self.left) + ' ' + self.op + '_' + str(self.ltime) + '^' + str(self.gtime) + ' ' + str(self.right) + ')'


class UntilFormula(BinaryTemporalFormula):
    op = 'U'


class ReleaseFormula(BinaryTemporalFormula):
    op = 'R'

