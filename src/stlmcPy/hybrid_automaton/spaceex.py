from functools import singledispatch
from typing import Union

from ..constraints.constraints import *


@singledispatch
def obj2se(const: Union[Formula, Expr], is_reset=False, is_initial=False):
    # return str(const)
    raise Exception("cannot support translation of {} for spaceex".format(const))


@obj2se.register(Variable)
def _(const: Variable, is_reset=False, is_initial=False):
    return const.id


@obj2se.register(Constant)
def _(const: Constant, is_reset=False, is_initial=False):
    return const.value


@obj2se.register(And)
def _(const: And, is_reset=False, is_initial=False):
    if is_initial:
        return ' & '.join([obj2se(c, is_reset, True) for c in const.children])
    return '&amp;'.join([obj2se(c, is_reset) for c in const.children])


@obj2se.register(Geq)
def _(const: Geq, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " >= " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &gt;= " + obj2se(const.right, is_reset)


@obj2se.register(Gt)
def _(const: Gt, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " > " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &gt; " + obj2se(const.right, is_reset)


@obj2se.register(Leq)
def _(const: Leq, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " <= " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &lt;= " + obj2se(const.right, is_reset)


@obj2se.register(Lt)
def _(const: Lt, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " < " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &lt; " + obj2se(const.right, is_reset)


@obj2se.register(Eq)
def _(const: Eq, is_reset=False, is_initial=False):
    if is_reset and not is_initial:
        if isinstance(const.left, Real):
            return "{}\' == {}".format(const.left.id, obj2se(const.right, True))
        elif isinstance(const.left, Int):
            return "{}\' == {}".format(const.left.id, obj2se(const.right, True))
        else:
            raise Exception("not supported {}".format(const.left.id))
    return obj2se(const.left, False, is_initial) + " == " + obj2se(const.right, False, is_initial)


# cannot support this
@obj2se.register(Neq)
def _(const: Neq, is_reset=False, is_initial=False):
    if is_initial:
        return obj2se(const.left, is_reset, True) + " >= " + obj2se(const.right, is_reset, True) + " & " \
               + obj2se(const.left, is_reset, True) + " < " + obj2se(const.right, is_reset, True)
    return obj2se(const.left, is_reset) + " &gt;= " + obj2se(const.right, is_reset) + " &amp; " \
           + obj2se(const.left, is_reset) + " &lt; " + obj2se(const.right, is_reset)


@obj2se.register(Add)
def _(const: Add, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " + " + obj2se(const.right, is_reset, is_initial) + ")"


@obj2se.register(Sub)
def _(const: Sub, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " - " + obj2se(const.right, is_reset, is_initial) + ")"


@obj2se.register(Neg)
def _(const: Neg, is_reset=False, is_initial=False):
    return "(-" + obj2se(const.child, is_reset, is_initial) + ")"


@obj2se.register(Mul)
def _(const: Mul, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " * " + obj2se(const.right, is_reset, is_initial) + ")"


@obj2se.register(Div)
def _(const: Div, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " / " + obj2se(const.right, is_reset, is_initial) + ")"


# maybe not supported
@obj2se.register(Pow)
def _(const: Pow, is_reset=False, is_initial=False):
    return "(" + obj2se(const.left, is_reset, is_initial) + " ** " + obj2se(const.right, is_reset, is_initial) + ")"

# @obj2se.register(Forall)
# def _(const: Forall):
#     return obj2se(const.const)
