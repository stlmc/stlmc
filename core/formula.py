from .base import *

class Formula:
    pass


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
    op = '/\\'


class OrFormula(Multiary, Formula):
    op = '\\/'


class ImpliesFormula(Binary, Formula):
    op = '->'


class UnaryTemporalFormula(Unary, Formula):
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


class BinaryTemporalFormula(Binary, Formula):
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

