from functools import singledispatch

from sympy import *

from ..constraints.constraints import *


@singledispatch
def obj2fs(const: Formula):
    raise Exception("fail to translate to flowstar object ({})".format(const))


@obj2fs.register(Variable)
def _(const: Variable):
    return const.id


@obj2fs.register(Constant)
def _(const: Constant):
    return const.value


@obj2fs.register(And)
def _(const: And):
    return '\n'.join([obj2fs(c) for c in const.children])


@obj2fs.register(Geq)
def _(const: Geq):
    return obj2fs(const.left - const.right) + " >= 0.0"


@obj2fs.register(Gt)
def _(const: Gt):
    return obj2fs(const.left - const.right) + " >= 0.0"


@obj2fs.register(Leq)
def _(const: Leq):
    return obj2fs(const.left - const.right) + " <= 0.0"


@obj2fs.register(Lt)
def _(const: Geq):
    return obj2fs(const.left - const.right) + " <= 0.0"


@obj2fs.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Real):
        return "{} = {}".format(const.left.id, obj2fs(const.right))
    elif isinstance(const.left, Int):
        return "{} = {}".format(const.left.id, obj2fs(const.right))
    else:
        raise Exception()


# cannot support this
@obj2fs.register(Neq)
def _(const: Geq):
    c1 = obj2fs(const.left - const.right) + " >= 0.0"
    c2 = obj2fs(const.left - const.right) + " <= 0.0"
    return c1 + "\n" + c2


@obj2fs.register(Add)
def _(const: Add):
    return "(" + obj2fs(const.left) + " + " + obj2fs(const.right) + ")"


@obj2fs.register(Sub)
def _(const: Sub):
    return "(" + obj2fs(const.left) + " - " + obj2fs(const.right) + ")"


@obj2fs.register(Neg)
def _(const: Neg):
    return "(-" + obj2fs(const.child) + ")"


@obj2fs.register(Mul)
def _(const: Mul):
    return "(" + obj2fs(const.left) + " * " + obj2fs(const.right) + ")"


@obj2fs.register(Div)
def _(const: Div):
    return "(" + obj2fs(const.left) + " / " + obj2fs(const.right) + ")"


# maybe not supported
@obj2fs.register(Pow)
def _(const: Pow):
    return "(" + obj2fs(const.left) + " ** " + obj2fs(const.right) + ")"


@obj2fs.register(Forall)
def _(const: Forall):
    return obj2fs(const.const)
