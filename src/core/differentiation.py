import itertools
from functools import singledispatch
from .error import *
from .node import *
from .z3Handler import *

def diff(expression):
    print("first diff")
    print(expression)
    return diff(expression)

@singledispatch
def diff(const:Node):
    raise NotImplementedError('Something wrong')

@diff.register(Constant)
def _(const):
    return RealVal(0) 

@diff.register(Variable)
def _(const):
    if str(const.id)[0:4] == 'time':
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
    if isinstance(const.left(), Variable) and z3.is_rational_value(z3.simplify(z3Obj(const.right()))) :
        if z3.simplify(z3Obj(const.right())) == 0:
            return RealVal(1)
        elif str(const.left().id[0:4] == 'time'):
            return (const.right() * (const.left() ** (const.right() - RealVal(1))))
        else:
            return RealVal(0)
    else:
        raise NotImplementedError('Cannot hanlindg polynomial yet')


@diff.register(Mul)
def _(const):
    x = const.left()
    y = const.right()
    return diff(x) * y + x * diff(y)

@diff.register(Div)
def _(const):
    x = const.left()
    y = const.right()
    return diff(x) / y - diff(y) * x / (y * y) 

@diff.register(Neg)
def _(const):
    x = diff(const.child())
    return -x


