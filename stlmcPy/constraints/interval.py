import math
from functools import singledispatch

from stlmcPy.constraints.constraints import *

def inIntervalCheck(j, b):
    if str(j.left) == str(b.left) and str(j.right) == str(b.right):
        return True
    if str(j.left) == str(j.right) and str(j.left) == str(b.left):
        return True
    return False


def inInterval(x: Constraint, j: Interval):
    assert isinstance(x, Expr)
    cl = x >= j.left if j.left_end else x > j.left
    if "inf" in str(j.right):
        return cl
    return And([cl, x <= j.right if j.right_end else x < j.right])


def subInterval(i: Interval, j: Interval):
    const = []

    if i.left_end and not j.left_end:
        const.append(i.left > j.left)
    else:
        const.append(i.left >= j.left)

    if not "inf" in str(i.right):
        if not "inf" in str(j.right):
            if i.right_end and not j.right_end:
                const.append(i.right < j.right)
            else:
                const.append(i.right <= j.right)
    else:
        if not (isinstance(j.right, Constant) and "inf" in str(j.right)):
            return And([BoolVal("False")])

    return And(const)


def minusInterval(i: Interval, j: Interval):
    left_end = False
    right_end = False
    if i.left_end and j.right_end:
        left_end = True
    if i.right_end and j.left_end:
        right_end = True

    left = i.left - j.right
    right = i.right - j.left
    return Interval(left_end, left, right_end, right)


def intervalConst(j: Interval, k: Interval, i: Interval):
    const = []

    if not "inf" in str(i.right):
        if j.left_end and not (k.left_end and i.right_end):
            const.append(j.left > (k.left - i.right))
        else:
            const.append(j.left >= (k.left - i.right))

    if not "inf" in str(j.right):
        if not "inf" in str(k.right):
            if j.right_end and not (k.right_end and i.left_end):
                const.append(j.right < (k.right - i.left))
            else:
                const.append(j.right <= (k.right - i.left))
    else:
        if not (isinstance(k.right, Constant) and "inf" in str(k.right)):
            return And([BoolVal("False")])

    return And(const)



