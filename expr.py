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
        return AndConstraint([self,other])
    def __or__(self, other):
        return OrConstraint([self,other])
    def __rshift__(self, other):
        return ImpliesConstraint(self, other)


class ConstantConstraint(Atomic, Constraint):
    pass


class NegConstraint(Unary, Constraint):
    op = '~'


class AndConstraint(Multiary, Constraint):
    op = '&'


class OrConstraint(Multiary, Constraint):
    op = '|'


class ImpliesConstraint(Binary, Constraint):
    op = '->'


class IffConstraint(Binary, Constraint):
    op = '<->'


class LessConstraint(Binary, Constraint):
    op = '<'


class EqualConstraint(Binary, Constraint):
    op = '=='


class Expr:
    def __add__(self, other):
        return AddExpr(self, other)
    def __sub__(self, other):
        return MinusExpr(self, other)
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


class VariableExpr(Atomic, Expr):
    pass


class ConstantExpr(Atomic, Expr):
    pass


class AddExpr(Binary, Expr):
    op = '+'


class MinusExpr(Binary, Expr):
    op = '-'

