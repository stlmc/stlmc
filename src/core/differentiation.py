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
    x = const.left()
    y = const.right()

    if z3.is_rational_value(z3.simplify(z3Obj(const))):
        return RealVal(0)
    if z3.is_rational_value(z3.simplify(z3Obj(const.left()))):
        return diff(y)
    if z3.is_rational_value(z3.simplify(z3Obj(const.right()))):
        return diff(x)

    return diff(x) + diff(y)

@diff.register(Minus)
def _(const):
    x = const.left()
    y = const.right()

    if z3.is_rational_value(z3.simplify(z3Obj(const))):
        return RealVal(0)
    if z3.is_rational_value(z3.simplify(z3Obj(const.left()))):
        return RealVal(0) - diff(y)
    if z3.is_rational_value(z3.simplify(z3Obj(const.right()))):
        return diff(x)

    return diff(x) - diff(y)

@diff.register(Pow)
def _(const):
    x = const.left()
    y = const.right()
    if z3.is_rational_value(z3.simplify(z3Obj(x))) and z3.is_rational_value(z3.simplify(z3Obj(y))):
        return RealVal(0)
    if isinstance(x, Variable) and z3.is_rational_value(z3.simplify(z3Obj(y))) :
        if z3.simplify(z3Obj(y)) == 0:
            return RealVal(0)
        elif str(x.id[0:4] == 'time'):
            return (y * (x ** (y - RealVal(1))))
        else:
            return RealVal(0)
    else:
        print(type(const))
        print(const)
        raise NotImplementedError('Cannot hanlindg polynomial yet')


@diff.register(Mul)
def _(const):
    x = const.left()
    y = const.right()
    if z3.is_rational_value(z3.simplify(z3Obj(const))):
        return RealVal(0)
    if z3.is_rational_value(z3.simplify(z3Obj(const.left()))):
        return x * diff(y)
    if z3.is_rational_value(z3.simplify(z3Obj(const.right()))):
        return diff(x) * y

    return diff(x) * y + x * diff(y)

@diff.register(Div)
def _(const):
    x = const.left()
    y = const.right()
    if z3.is_rational_value(z3.simplify(z3Obj(const))):
        return RealVal(0)
    if z3.is_rational_value(z3.simplify(z3Obj(const.left()))):
        return RealVal(0) - diff(y) * x / (y * y)
    if z3.is_rational_value(z3.simplify(z3Obj(const.right()))):
        return diff(x) / y


    return diff(x) / y - diff(y) * x / (y * y) 

@diff.register(Neg)
def _(const):
    x = diff(const.child())
    return -x


