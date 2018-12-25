import math
from .base import Interval
from .constraint import *
import z3

def inIntervalC(x:float, j:Interval):
    return (x >= j.left  if j.leftend  else x > j.left) and (x <= j.right if j.rightend else x < j.right)

def intervalConstC(j:Interval, k:Interval, i:Interval):
    if j.leftend and not (k.leftend and i.rightend):
        if not (j.left >  k.left - i.right):
            return False
    else:
        if not (j.left >= k.left - i.right):
            return False

    if j.rightend and not (k.rightend and i.leftend):
        if not (j.right <  k.right - i.left):
            return False
    else:
        if not (j.right <= k.right - i.left):
            return False
    return True

def inInterval(x:ArithRef, j:Interval):
    """
    return a constraint for x \in j

    >>> inInterval(RealVal(1.5), Interval(True, 1.0, True,  2.0))
    And(3/2 >= 1, 3/2 <= 2)
    >>> inInterval(Real('x'), Interval(True, 1.0, False,  2.0))
    And(1 <= x, 2 > x)
    >>> inInterval(RealVal(1.0), Interval(True, 0.0, False, float('inf')))
    1 >= 0
    """

    cl = x >= RealVal(j.left) if j.leftend else x >  RealVal(j.left)

    if math.isfinite(j.right):
        return And(cl, x <= RealVal(j.right) if j.rightend else x < RealVal(j.right))
    else:
        return cl


def subInterval(i:Interval, j:Interval):
    const = []
    if i.leftend and not j.leftend:
        const.append(_real(i.left) >  _real(j.left))
    else:
        const.append(_real(i.left) >= _real(j.left))

    if not isinstance(i.right, float) or math.isfinite(i.right):
        if not isinstance(j.right, float) or math.isfinite(j.right):
            if i.rightend and not j.rightend:
                const.append(_real(i.right) <  _real(j.right))
            else:
                const.append(_real(i.right) <= _real(j.right))
    else:
        if not (isinstance(j.right, float) and math.isinf(j.right)):
            return BoolVal(False)

    return And(*const)


def intervalConst(j:Interval, k:Interval, i:Interval):
    const = []

    if isinstance(j.left, ArithRef):
        const.append(_real(j.left) >= RealVal(0))

    if math.isfinite(i.right):
        if j.leftend and not (k.leftend and i.rightend):
            const.append(_real(j.left) >  (_real(k.left) - _real(i.right)))
        else:
            const.append(_real(j.left) >= (_real(k.left) - _real(i.right)))

    if not isinstance(j.right, float) or math.isfinite(j.right):
        if not isinstance(k.right, float) or math.isfinite(k.right):
            if j.rightend and not (k.rightend and i.leftend):
                const.append(_real(j.right) <  (_real(k.right) - _real(i.left)))
            else:
                const.append(_real(j.right) <= (_real(k.right) - _real(i.left)))
    else:
        if not (isinstance(k.right, float) and math.isinf(k.right)):
            return BoolVal(False)

    return And(*const)


def _real(x):
    if isinstance(x, ArithRef):
        return x
    elif isinstance(x, float):
        return RealVal(x)
    elif type(x) is str:
        return Real(x)
    else:
        raise RuntimeError("Invalid partition : " + str(x)) 


