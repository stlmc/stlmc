import itertools
import math
from functools import singledispatch

# We add linear order constraints for separation only
from .interval import inInterval
from .operations import generate_id
from .constraints import *

# We add linear order constraints for separation only

def baseCase(baseSize):
    genVar = generate_id(1, "tau_")
    return [Real(next(genVar)) for _ in range(baseSize)]


def guessPartition(formula, baseCase):
    result = {}
    sepMap = {}
    bConst = []
    genVar = generate_id(0, "TauIndex")

    # add order constraints based on base partition (ex . tau_0 < tau_1 ...) to bConst
    _addConstOrd(baseCase, genVar, bConst, True)
    _guess(formula, baseCase, genVar, result, sepMap, bConst)

    return (result, sepMap, bConst)


@singledispatch
def _guess(formula, baseCase, genVar, result, sepMap, const):
    raise NotImplementedError('Something wrong')


@_guess.register(Constant)
def _(formula, baseCase, genVar, result, sepMap, const):
    result[formula] = set()


@_guess.register(Bool)
def _(formula, baseCase, genVar, result, sepMap, const):
    result[formula] = set(baseCase)


@_guess.register(Not)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.child, baseCase, genVar, result, sepMap, const)
    result[formula] = result[formula.child]


@_guess.register(MultinaryFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    for c in formula.children:
        _guess(c, baseCase, genVar, result, sepMap, const)
    result[formula] = set(itertools.chain.from_iterable([result[c] for c in formula.children]))


@_guess.register(Implies)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.left, baseCase, genVar, result, sepMap, const)
    _guess(formula.right, baseCase, genVar, result, sepMap, const)
    result[formula] = result[formula.left] | result[formula.right]


@_guess.register(UnaryTemporalFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.child, baseCase, genVar, result, sepMap, const)

    p = result[formula.child]
    sepMap[formula] = [Real(next(genVar)) for _ in range(len(p))]
    result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}

    _addConstOrd(sepMap[formula], genVar, const)
    _addConstEqu(sepMap[formula], p, const)
    _addConstPar(result[formula], p, formula.global_time, formula.local_time, const)


@_guess.register(BinaryTemporalFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.left, baseCase, genVar, result, sepMap, const)
    _guess(formula.right, baseCase, genVar, result, sepMap, const)

    p = result[formula.left] | result[formula.right]
    sepMap[formula] = [Real(next(genVar)) for _ in range(len(p))]
    result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}

    _addConstOrd(sepMap[formula], genVar, const)
    _addConstEqu(sepMap[formula], p, const)
    _addConstPar(result[formula], p, formula.global_time, formula.local_time, const)


def _addConstOrd(bCase, genVar, bConst, strict=False):
    # op = ArithRef.__lt__ if strict else ArithRef.__le__
    if strict:
        bConst.extend([Lt(bCase[i], bCase[i+1]) for i in range(len(bCase)-1)])
    else:
        bConst.extend([Leq(bCase[i], bCase[i+1]) for i in range(len(bCase)-1)])


def _addConstEqu(wl, yl, const):
    for w in wl:
        const.append(Or([Eq(w, y) for y in yl]))
    for y in yl:
        const.append(Or([Eq(y, w) for w in wl]))

# result[formula], result[formula.child], formula.gtime, formula.ltime, const)
def _addConstPar(wl, yl, k:Interval, i:Interval, const):
    def _constEnd(w, y):
        arg = [Eq(w, RealVal("0"))] + [Eq(w, y - RealVal(str(e))) for e in [i.left,i.right] if math.isfinite(float(e.value))]
        return Or(arg)
    for w in wl:
        arg = [And([inInterval(y, k), _constEnd(w, y)]) for y in yl] + [_constEnd(w, e) for e in [k.left, k.right] if math.isfinite(float(e.value))]
        const.append(Or(arg))
        const.append(w >= RealVal("0"))
    const.extend([Implies(And([inInterval(y,k), y - e >= RealVal("0")]), Or([Eq(w, y - e) for w in wl])) \
            for y in yl for e in [i.left, i.right] if math.isfinite(float(e.value))])
    const.extend([Implies(e1 - e2 >= RealVal("0"), Or([Eq(w, e1 - e2) for w in wl])) \
            for e1 in [k.left, k.right] if math.isfinite(float(e1.value)) for e2 in [i.left, i.right] if math.isfinite(float(e2.value))])
