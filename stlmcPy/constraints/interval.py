import math
from functools import singledispatch

from stlmcPy.constraints.constraints import *


def inIntervalC(x: float, j: Interval):
    return (x >= j.left if j.left_end else x > j.left) and (x <= j.right if j.right_end else x < j.right)


def inIntervalCheck(j, b):
    if str(j.left) == str(b.left) and str(j.right) == str(b.right):
        return True
    if str(j.left) == str(j.right) and str(j.left) == str(b.left):
        return True
    return False


def intervalConstC(j: Interval, k: Interval, i: Interval):
    if j.left_end and not (k.left_end and i.right_end):
        if not (j.left > k.left - i.right):
            return False
    else:
        if not (j.left >= k.left - i.right):
            return False

    if j.right_end and not (k.right_end and i.left_end):
        if not (j.right < k.right - i.left):
            return False
    else:
        if not (j.right <= k.right - i.left):
            return False
    return True


def aux_inInterval(x: Constraint, j: Interval):
    if isinstance(j.left, float):
        left = RealVal(str(j.left))
    else:
        left = j.left

    if isinstance(j.right, float):
        right = RealVal(str(j.right))
    else:
        right = j.right
    cl = x >= left if j.left_end else x > left
    if isinstance(j.right, float):
        if not math.isfinite(j.right):
            return cl
    return And([cl, x <= right if j.right_end else x < right])


@singledispatch
def inInterval(x: Real, j: Interval):
    """
    return a constraint for x \in j

    >>> inInterval(RealVal(1.5), Interval(True, 1.0, True,  2.0))
    And(3/2 >= 1, 3/2 <= 2)
    >>> inInterval(Real('x'), Interval(True, 1.0, False,  2.0))
    And(1 <= x, 2 > x)
    >>> inInterval(RealVal(1.0), Interval(True, 0.0, False, float('inf')))
    1 >= 0
    """
    return aux_inInterval(x, j)


@inInterval.register(RealVal)
def _(x: RealVal, j: Interval):
    return aux_inInterval(x, j)


@inInterval.register(Int)
def _(x: Int, j: Interval):
    return aux_inInterval(x, j)


@inInterval.register(IntVal)
def _(x: IntVal, j: Interval):
    return aux_inInterval(x, j)


def subInterval(i: Interval, j: Interval):
    const = []
    if i.left_end and not j.left_end:
        const.append(_real(i.left) > _real(j.left))
    else:
        const.append(_real(i.left) >= _real(j.left))

    if not isinstance(i.right, float) or math.isfinite(i.right):
        if not isinstance(j.right, float) or math.isfinite(j.right):
            if i.right_end and not j.right_end:
                const.append(_real(i.right) < _real(j.right))
            else:
                const.append(_real(i.right) <= _real(j.right))
    else:
        if not (isinstance(j.right, float) and math.isinf(j.right)):
            return And([BoolVal("False")])

    return And(const)

def minusInterval(i: Interval, j: Interval):
    left_end = False
    right_end = False
    if i.left_end and j.left_end:
        left_end = True
    if i.right_end and j.right_end:
        right_end = True

    i_left_val = i.left
    if isinstance(i.left, float):
        i_left_val = RealVal(str(i.left))
    i_right_val = i.right
    if isinstance(i.right,float):
        i_right_val = RealVal(str(i.right))

    j_left_val = j.left
    if isinstance(j.left, float):
        j_left_val = RealVal(str(j.left))
    i_right_val = i.right
    if isinstance(j.right,float):
        j_right_val = RealVal(str(j.right))
    left = i_left_val - j_right_val
    right = i_right_val - j_left_val
    return Interval(left_end, left, right_end, right)

def intervalConst(j: Interval, k: Interval, i: Interval):
    const = []
    if not isinstance(j.right, float) or math.isfinite(j.right):
        mid = (_real(j.left) + _real(j.right)) / RealVal("2")
    else:
        mid = (_real(j.left) + RealVal("1"))

    if isinstance(j.left, Real) or isinstance(j.left, RealVal) \
            or isinstance(j.left, Int) or isinstance(j.left, IntVal):
        const.append(_real(j.left) >= RealVal("0"))

    if math.isfinite(i.right):
        if j.left_end and not (k.left_end and i.right_end):
            const.append(mid > (_real(k.left) - _real(i.right)))
        else:
            const.append(mid >= (_real(k.left) - _real(i.right)))

    if not isinstance(j.right, float) or math.isfinite(j.right):
        if not isinstance(k.right, float) or math.isfinite(k.right):
            if j.right_end and not (k.right_end and i.left_end):
                const.append(mid < (_real(k.right) - _real(i.left)))
            else:
                const.append(mid <= (_real(k.right) - _real(i.left)))
    else:
        if not (isinstance(k.right, float) and math.isinf(k.right)):
            return And([BoolVal("False")])

    return And(const)


def _real(x):
    if isinstance(x, Real):
        return x
    elif isinstance(x, RealVal):
        return x
    elif isinstance(x, Int):
        return x
    elif isinstance(x, IntVal):
        return x
    elif isinstance(x, float):
        return RealVal(str(x))
    elif isinstance(x, int):
        return IntVal(str(x))
    elif type(x) is str:
        return Real(str(x))
    else:
        print(type(x))
        raise RuntimeError("Invalid partition : " + str(x))
