
import math, itertools
from base import genId
from formula import *
from const import *

from functools import singledispatch

# We add linear order constraints for separation only

def baseCase(baseSize):
    genVar = genId(0, "tau_")
    return [z3.Real(next(genVar)) for _ in range(baseSize)]


def guessPartition(formula, baseCase):
    result = {}
    sepMap = {}
    bConst = []
    genVar = genId(0)

    _addConstOrd(baseCase, genVar, bConst, True)

    _guess(formula, baseCase, genVar, result, sepMap, bConst)

    return (result, sepMap, bConst)


@singledispatch
def _guess(formula, baseCase, genVar, result, sepMap, const):
    raise NotImplementedError('Something wrong')

@_guess.register(ConstantFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    result[formula] = set()

@_guess.register(PropositionFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    result[formula] = set(baseCase)

@_guess.register(NotFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.child, baseCase, genVar, result, sepMap, const)
    result[formula] = result[formula.child]

@_guess.register(Multiary)
def _(formula, baseCase, genVar, result, sepMap, const):
    for c in formula.children:
        _guess(c,  baseCase, genVar, result, sepMap, const)
    result[formula] = set(itertools.chain.from_iterable([result[c] for c in formula.children]))

@_guess.register(ImpliesFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.left,  baseCase, genVar, result, sepMap, const)
    _guess(formula.right, baseCase, genVar, result, sepMap, const)
    result[formula] = result[formula.left] | result[formula.right]


@_guess.register(UnaryTemporalFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.child, baseCase, genVar, result, sepMap, const)

    p = result[formula.child]
    sepMap[formula] = [z3.Real(next(genVar)) for _ in range(len(p))]
    result[formula] = {z3.Real(next(genVar)) for _ in range(2 * (len(p) + 2))}
    

    _addConstOrd(sepMap[formula], genVar, const)
    _addConstEqu(sepMap[formula], p, const)
    _addConstPar(result[formula], p, formula.gtime, formula.ltime, const)


@_guess.register(BinaryTemporalFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.left,  baseCase, genVar, result, sepMap, const)
    _guess(formula.right, baseCase, genVar, result, sepMap, const)

    p = result[formula.left] | result[formula.right]
    sepMap[formula] = [z3.Real(next(genVar)) for _ in range(len(p))]
    result[formula] = {z3.Real(next(genVar)) for _ in range(2 * (len(p) + 2))}

    _addConstOrd(sepMap[formula], genVar, const)
    _addConstEqu(sepMap[formula], p, const)
    _addConstPar(result[formula], p, formula.gtime, formula.ltime, const)


def _addConstOrd(bCase, genVar, bConst, strict=False):
    op = z3.ArithRef.__lt__ if strict else z3.ArithRef.__le__
    bConst.extend([op(bCase[i], bCase[i+1]) for i in range(len(bCase)-1)])


def _addConstEqu(wl, yl, const):
    for w in wl:
        const.append(z3.Or([w == y for y in yl]))
    for y in yl:
        const.append(z3.Or([y == w for w in wl]))


def _addConstPar(wl, yl, k:Interval, i:Interval, const):
    def _constEnd(w, y):
        return z3.Or([w == z3.RealVal(0)] + [w == y - z3.RealVal(e) for e in [i.left,i.right] if math.isfinite(e)])

    for w in wl:
        const.append(z3.Or(\
                [z3.And(inInterval(y, k), _constEnd(w, y)) for y in yl] + \
                [_constEnd(w, z3.RealVal(e)) for e in [k.left, k.right] if math.isfinite(e)]))
        const.append(w >= z3.RealVal(0))

    const.extend([z3.Implies(z3.And(inInterval(y,k), y - RealVal(e) >= 0), z3.Or([w == y - z3.RealVal(e) for w in wl])) \
            for y in yl for e in [i.left, i.right] if math.isfinite(e)])
    const.extend([z3.Implies(z3.RealVal(e1) - z3.RealVal(e2) >= 0, z3.Or([w == z3.RealVal(e1) - z3.RealVal(e2) for w in wl])) \
            for e1 in [k.left, k.right] if math.isfinite(e1) for e2 in [i.left, i.right] if math.isfinite(e2)])
