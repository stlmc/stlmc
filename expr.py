"""
Simple implementation of expressions and constraints. For example:

>>> a = ConstantExpr(1.0)
>>> b = ConstantExpr(2.0)
>>> x = VariableExpr('x')
>>> y = VariableExpr('y')
>>> print(a)
1.0
>>> print(a + x)
(1.0 + x)
>>> print(a < b)
(1.0 < 2.0)
>>> print(~ (a < b))
(~ (1.0 < 2.0))
>>> print((a + x) > (y - b))
(~ (((1.0 + x) < (y - 2.0)) | ((1.0 + x) == (y - 2.0))))
"""

from base import *

class Constraint:
    def __invert__(self):
        return NegConstraint(self)
    def __and__(self, other):
        return AndConstraint(self,other)
    def __or__(self, other):
        return OrConstraint(self,other)


class NegConstraint(Constraint,Unary):
    op = '~'


class BinaryConstraint(Constraint,Binary):
    pass


class AndConstraint(BinaryConstraint):
    op = '&'


class OrConstraint(BinaryConstraint):
    op = '|'


class LessConstraint(BinaryConstraint):
    op = '<'


class EqualConstraint(BinaryConstraint):
    op = '=='


class Expr:
    def __add__(self, other):
        return AddExpr(self, other)
    def __sub__(self, other):
        return MonusExpr(self, other)
    def __lt__(self, other):
        return LessConstraint(self,other)
    def __le__(self, other):
        return (self < other) | (self == other)
    def __eq__(self, other):
        return EqualConstraint(self,other)
    def __ne__(self, other):
        return ~(self != other)
    def __ge__(self, other):
        return ~(self < other)
    def __gt__(self, other):
        return ~(self <= other)


class VariableExpr(Expr,Atomic):
    pass


class ConstantExpr(Expr,Atomic):
    pass


class BinaryExpr(Expr,Binary):
    pass


class AddExpr(BinaryExpr):
    op = '+'


class MonusExpr(BinaryExpr):
    op = '-'

