import itertools
from functools import singledispatch
from .error import *
from .node import *


# return a check result and the Z3 constraint size
def diff(expression):
    return diff(expression)

@singledispatch
def diff(const:Node):
    raise NotImplementedError('Something wrong')

@diff.register(Constant)
def _(const):
    return RealVal(0) 

@diff.register(Variable)
def _(const):
    if str(const.id) == 'time':
        return RealVal(1)
    else:
        return RealVal(0)

@diff.register(Plus)
def _(const):
    x = diff(const.left())
    y = diff(const.right())
    return x + y

@diff.register(Minus)
def _(const):
    x = diff(const.left())
    y = diff(const.right())
    return x - y

@diff.register(Pow)
def _(const):
    if isinstance(const.left(), Variable) and isinstance(const.right(), Constant) :
        if str(const.left().id == 'time'):
            const.right() * const.left() ** (const.right() - RealVal(1))
        else:
            return RealVal(0)
    else:
        raise NotImplementedError('Something wrong')


@diff.register(Mul)
def _(const):
    x = const.left()
    y = const.right()
    return diff(x) * y + x * diff(y)

@diff.register(Div)
def _(const):
    x = const.left()
    y = const.right()
    return -diff(y) * x / (y * y) + diff(x) / y

@diff.register(Neg)
def _(const):
    x = diff(const.child())
    return -x


