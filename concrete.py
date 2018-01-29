
import math, itertools
from formula import *
from const import inIntervalC, intervalConstC

from functools import singledispatch


def buildPartition(formula, baseCase):
    result = {}
    _build(formula, baseCase, result)
    return result

@singledispatch
def _build(formula, baseCase, result):
    raise NotImplementedError('Something wrong')

@_build.register(ConstantFormula)
def _(formula, baseCase, result):
    result[formula] = []

@_build.register(PropositionFormula)
def _(formula, baseCase, result):
    result[formula] = baseCase

@_build.register(NotFormula)
def _(formula, baseCase, result):
    _build(formula.child, baseCase, result)
    result[formula] = result[formula.child]

@_build.register(Multiary)
def _(formula, baseCase, result):
    for c in formula.children:
        _build(c,  baseCase, result)
    result[formula] = list(itertools.chain.from_iterable([result[c] for c in formula.children]))

@_build.register(ImpliesFormula)
def _(formula, baseCase, result):
    _build(formula.left,  baseCase, result)
    _build(formula.right, baseCase, result)
    result[formula] = result[formula.left] + result[formula.right]

@_build.register(UnaryTemporalFormula)
def _(formula, baseCase, result):
    _build(formula.child, baseCase, result)
    p = [x for x in result[formula.child] if inIntervalC(x,formula.gtime)]
    p.extend([formula.gtime.left,formula.gtime.right])
    result[formula] = list(filter(lambda x: math.isfinite(x) and x >= 0,\
            [x-formula.ltime.left for x in p] + [x-formula.ltime.right for x in p]))
    

@_build.register(BinaryTemporalFormula)
def _(formula, baseCase, result):
    _build(formula.left,  baseCase, result)
    _build(formula.right, baseCase, result)
    p = [x for x in result[formula.left] + result[formula.right] if inIntervalC(x,formula.gtime)]
    p.extend([formula.gtime.left,formula.gtime.right])
    result[formula] = list(filter(lambda x: math.isfinite(x) and x >= 0,\
            [x-formula.ltime.left for x in p] + [x-formula.ltime.right for x in p]))


@singledispatch
def valuation(f:Formula, j:Interval, bp, bv):
    raise NotImplementedError('Something wrong')

@valuation.register(ConstantFormula)
def _(f:Formula, j:Interval, bp, bv):
    return f.getValue()

@valuation.register(PropositionFormula)
def _(f:Formula, j:Interval, bp, bv):
    return True

@valuation.register(NotFormula)
def _(f:Formula, j:Interval, bp, bv):
    return not(valuation(f.child, j, bp, bv))

@valuation.register(Multiary)
def _(f:Formula, j:Interval, bp, bv):
    op = {AndFormula: all, OrFormula: any}
    return op[f.__class__]([valuation(c, j, bp, bv) for c in f.children])

@valuation.register(ImpliesFormula)
def _(f:Formula, j:Interval, bp, bv):
    return not valuation(f.left, j, bp, bv) or valuation(f.right, j, bp, bv)

@valuation.register(FinallyFormula)
def _(f:Formula, j:Interval, bp, bv):
    return intervalConstC(j,f.gtime,f.ltime) and valuation(f.child, f.gtime, bp, bv)

@valuation.register(GloballyFormula)
def _(f:Formula, j:Interval, bp, bv):
    return not intervalConstC(j,f.gtime,f.ltime) or valuation(f.child, f.gtime, bp, bv)

@valuation.register(UntilFormula)
def _(f:Formula, j:Interval, bp, bv):
    return intervalConstC(j,f.gtime,f.ltime) and valuation(f.left, f.gtime, bp, bv) and valuation(f.right, f.gtime, bp, bv)

@valuation.register(ReleaseFormula)
def _(f:Formula, j:Interval, bp, bv):
    return not(intervalConstC(j,f.gtime,f.ltime)) or valuation(f.left, f.gtime, bp, bv) or valuation(f.right, f.gtime, bp, bv)

