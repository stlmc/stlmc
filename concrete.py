
import math, itertools, bisect
from formula import *
from const import inIntervalC, intervalConstC

from functools import singledispatch


def buildPartition(formula, baseCase):
    result = {}
    sepMap = {}
    _build(formula, baseCase, result, sepMap)
    return (result, sepMap)

@singledispatch
def _build(formula, baseCase, result, sepMap):
    raise NotImplementedError('Something wrong')

@_build.register(ConstantFormula)
def _(formula, baseCase, result, sepMap):
    result[formula] = set()

@_build.register(PropositionFormula)
def _(formula, baseCase, result, sepMap):
    result[formula] = set(baseCase)

@_build.register(NotFormula)
def _(formula, baseCase, result, sepMap):
    _build(formula.child, baseCase, result, sepMap)
    result[formula] = result[formula.child]

@_build.register(Multiary)
def _(formula, baseCase, result, sepMap):
    for c in formula.children:
        _build(c,  baseCase, result, sepMap)
    result[formula] = set(itertools.chain.from_iterable([result[c] for c in formula.children]))

@_build.register(ImpliesFormula)
def _(formula, baseCase, result, sepMap):
    _build(formula.left,  baseCase, result, sepMap)
    _build(formula.right, baseCase, result, sepMap)
    result[formula] = result[formula.left] | result[formula.right]

@_build.register(UnaryTemporalFormula)
def _(formula, baseCase, result, sepMap):
    _build(formula.child, baseCase, result, sepMap)
    p = {x for x in result[formula.child] if inIntervalC(x,formula.gtime)}
    p.update([formula.gtime.left,formula.gtime.right])
    sepMap[formula] = sorted(p)
    result[formula] = set(filter(lambda x: math.isfinite(x) and x >= 0,\
            {x-formula.ltime.left for x in p} | {x-formula.ltime.right for x in p}))
    

@_build.register(BinaryTemporalFormula)
def _(formula, baseCase, result, sepMap):
    _build(formula.left,  baseCase, result, sepMap)
    _build(formula.right, baseCase, result, sepMap)
    p = {x for x in result[formula.left] | result[formula.right] if inIntervalC(x,formula.gtime)}
    p.update([formula.gtime.left,formula.gtime.right])
    sepMap[formula] = sorted(p)
    result[formula] = set(filter(lambda x: math.isfinite(x) and x >= 0,\
            {x-formula.ltime.left for x in p} | {x-formula.ltime.right for x in p}))

def valuation(f:Formula, sub:dict, j:Interval, bp, bv):
    vMap = {}
    result = _value(f, sub, j, bp, bv, vMap)
    return result

@singledispatch
def _value(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    raise NotImplementedError('Something wrong')

@_value.register(ConstantFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    return f.getValue()

@_value.register(PropositionFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    if f in sub:
        if not (f,j) in vMap:
            vMap[(f,j)] = _value(sub[f], sub, j, bp, bv, vMap)
        return vMap[(f,j)]
    else:
        return bv[f][bisect.bisect_right(bp, (j.left + j.right)/2)-1]

@_value.register(NotFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    return not(_value(f.child, sub, j, bp, bv, vMap))

@_value.register(AndFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    for c in f.children:
        if not _value(c, sub, j, bp, bv, vMap):
            return False
    return True

@_value.register(OrFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    for c in f.children:
        if _value(c, sub, j, bp, bv, vMap):
            return True
    return False

@_value.register(ImpliesFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    return not _value(f.left, sub, j, bp, bv, vMap) or _value(f.right, sub, j, bp, bv, vMap)

@_value.register(FinallyFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    return intervalConstC(j,f.gtime,f.ltime) and _value(f.child, sub, f.gtime, bp, bv, vMap)

@_value.register(GloballyFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    return not intervalConstC(j,f.gtime,f.ltime) or _value(f.child, sub, f.gtime, bp, bv, vMap)

@_value.register(UntilFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    return intervalConstC(j,f.gtime,f.ltime) and _value(f.left, sub, f.gtime, bp, bv, vMap) and _value(f.right, sub, f.gtime, bp, bv, vMap)

@_value.register(ReleaseFormula)
def _(f:Formula, sub:dict, j:Interval, bp, bv, vMap):
    return not(intervalConstC(j,f.gtime,f.ltime)) or _value(f.left, sub, f.gtime, bp, bv, vMap) or _value(f.right, sub, f.gtime, bp, bv, vMap)

