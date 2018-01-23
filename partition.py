
import math, itertools
from base import genId
from formula import *
from const import *

from functools import singledispatch


def guessPartition(formula, baseSize):
    result = {}
    genVar = genId(0)

    bConst = []
    bCase = _genVar(baseSize, genVar, bConst, True)

    _guess(formula, bCase, genVar, result, bConst)

    return (result, bConst)


@singledispatch
def _guess(formula, baseCase, genVar, result, const):
    raise NotImplementedError('Something wrong')

@_guess.register(ConstantFormula)
def _(formula, baseCase, genVar, result, const):
    result[formula] = []

@_guess.register(PropositionFormula)
def _(formula, baseCase, genVar, result, const):
    result[formula] = baseCase

@_guess.register(NotFormula)
def _(formula, baseCase, genVar, result, const):
    _guess(formula.child, baseCase, genVar, result, const)
    result[formula] = result[formula.child]

@_guess.register(Multiary)
def _(formula, baseCase, genVar, result, const):
    for c in formula.children:
        _guess(c,  baseCase, genVar, result, const)
    result[formula] = list(itertools.chain.from_iterable([result[c] for c in formula.children]))

@_guess.register(ImpliesFormula)
def _(formula, baseCase, genVar, result, const):
    _guess(formula.left,  baseCase, genVar, result, const)
    _guess(formula.right, baseCase, genVar, result, const)
    result[formula] = result[formula.left] + result[formula.right]

@_guess.register(UnaryTemporalFormula)
def _(formula, baseCase, genVar, result, const):
    _guess(formula.child, baseCase, genVar, result, const)
    result[formula]  = _genVar(2 * (len(result[formula.child]) + 2), genVar, const)
    _addConst1(result[formula], result[formula.child], formula.gtime, formula.ltime, const)
    _addConst2(result[formula], result[formula.child], formula.gtime, formula.ltime, const)

@_guess.register(BinaryTemporalFormula)
def _(formula, baseCase, genVar, result, const):
    _guess(formula.left,  baseCase, genVar, result, const)
    _guess(formula.right, baseCase, genVar, result, const)
    result[formula]  = _genVar(2 * (len(result[formula.left]) + len(result[formula.right]) + 2), genVar, const)
    _addConst1(result[formula], result[formula.left] + result[formula.right], formula.gtime, formula.ltime, const)
    _addConst2(result[formula], result[formula.left] + result[formula.right], formula.gtime, formula.ltime, const)


def _genVar(size, genVar, bConst, strict=False):
    op = ArithRef.__lt__ if strict else ArithRef.__le__
    bCase = [Real(next(genVar)) for _ in range(size)]
    bConst.extend([op(bCase[i], bCase[i+1]) for i in range(size-1)])
    return bCase 


def _addConst1(wl, yl, k:Interval, i:Interval, const):
    def _constEnd(w, y):
        return Or([w == RealVal(0)] + [w == y - RealVal(e) for e in [i.left,i.right] if math.isfinite(e)])

    for w in wl:
        const.append(Or(\
                [And(inInterval(y, k), _constEnd(w, y)) for y in yl] + \
                [_constEnd(w, RealVal(e)) for e in [k.left, k.right] if math.isfinite(e)]))
        const.append(w >= RealVal(0))


def _addConst2(wl, yl, k:Interval, i:Interval, const):
    const.extend([Implies(And(inInterval(y,k), y - RealVal(e) >= 0), Or([w == y - RealVal(e) for w in wl])) \
            for y in yl for e in [i.left, i.right] if math.isfinite(e)])
    const.extend([Implies(RealVal(e1) - RealVal(e2) >= 0, Or([w == RealVal(e1) - RealVal(e2) for w in wl])) \
            for e1 in [k.left, k.right] if math.isfinite(e1) for e2 in [i.left, i.right] if math.isfinite(e2)])


