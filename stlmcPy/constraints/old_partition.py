from .constraints import *
from .operations import generate_id, get_vars
from functools import singledispatch


# We add linear order constraints for separation only

def baseCase(baseSize):
    genVar = generate_id(1, "tau_")
    return [Real(next(genVar)) for _ in range(baseSize)]


def guessPartition(formula, baseCase):
    result = {}
    sepMap = {}
    bConst = []
    genVar = genId(0, "TauIndex")

    # add order constraints based on base partition (ex . tau_0 < tau_1 ...) to bConst
    _addConstOrd(baseCase, genVar, bConst, True)
    _guess(formula, baseCase, genVar, result, sepMap, bConst)

    return (result, sepMap, bConst)


@singledispatch
def _guess(formula, baseCase, result, sepMap):
    raise NotImplementedError('Something wrong')


@_guess.register(Constant)
def _(formula, baseCase, result, sepMap):
    result[formula] = set()


@_guess.register(Bool)
def _(formula, baseCase, result, sepMap):
    result[formula] = set(baseCase)


@_guess.register(Not)
def _(formula, baseCase, result, sepMap):
    _guess(formula.child, baseCase, result, sepMap)
    result[formula] = result[formula.child]
    # result[formula] = set(baseCase)


@_guess.register(MultinaryFormula)
def _(formula, baseCase, result, sepMap):
    for c in formula.children:
        _guess(c, baseCase, result, sepMap)
    result[formula] = set(itertools.chain.from_iterable([result[c] for c in formula.children]))
    # result[formula] = set(baseCase)


@_guess.register(Implies)
def _(formula, baseCase, result, sepMap):
    _guess(formula.left, baseCase, result, sepMap)
    _guess(formula.right, baseCase, result, sepMap)
    result[formula] = result[formula.left] | result[formula.right]
    # result[formula] = set(baseCase)


@_guess.register(UnaryTemporalFormula)
def _(formula, baseCase, result, sepMap):
    _guess(formula.child, baseCase, result, sepMap)

    p = result[formula.child]
    sepMap[formula] = [Real(next(genVar)) for _ in range(len(p))]
    # sepMap[formula] = baseCase

    result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}
    # result[formula] = set(baseCase)
    _addConstOrd(sepMap[formula], genVar, const)
    _addConstEqu(sepMap[formula], p, const)
    _addConstPar(result[formula], p, formula.gtime, formula.ltime, const)


@_guess.register(BinaryTemporalFormula)
def _(formula, baseCase, result, sepMap):
    _guess(formula.left, baseCase, result, sepMap)
    _guess(formula.right, baseCase, result, sepMap)

    p = result[formula.left] | result[formula.right]
    sepMap[formula] = [Real(next(genVar)) for _ in range(len(p))]
    # sepMap[formula] = baseCase

    result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}
    # result[formula] = set(baseCase)
    _addConstOrd(sepMap[formula], genVar, const)
    _addConstEqu(sepMap[formula], p, const)
    _addConstPar(result[formula], p, formula.gtime, formula.ltime, const)

def _addConstOrd(bCase, genVar, bConst, strict=False):
    # op = ArithRef.__lt__ if strict else ArithRef.__le__
    if strict:
        bConst.extend([Lt(bCase[i], bCase[i+1]) for i in range(len(bCase)-1)])
    else:
        bConst.extend([Leq(bCase[i], bCase[i+1]) for i in range(len(bCase)-1)])


def _addConstEqu(wl, yl, const):
    for w in wl:
        const.append(Or([w == y for y in yl]))
    for y in yl:
        const.append(Or([y == w for w in wl]))

# result[formula], result[formula.child], formula.gtime, formula.ltime, const)
def _addConstPar(wl, yl, k:Interval, i:Interval, const):
    def _constEnd(w, y):
        arg = [w == RealVal("0")] + [w == y - RealVal(str(e)) for e in [i.left,i.right] if math.isfinite(e)]
        return Or(arg)
    for w in wl:
        arg = [And(inInterval(y, k), _constEnd(w, y)) for y in yl] + [_constEnd(w, RealVal(str(e))) for e in [k.left, k.right] if math.isfinite(e)]
        const.append(Or(arg))
        const.append(w >= RealVal("0"))
    const.extend([Implies(And([inInterval(y,k), y - RealVal(str(e)) >= RealVal("0")]), Or([w == y - RealVal(str(e)) for w in wl])) \
            for y in yl for e in [i.left, i.right] if math.isfinite(e)])
    const.extend([Implies(RealVal(str(e1)) - RealVal(str(e2)) >= RealVal("0"), Or([w == RealVal(str(e1)) - RealVal(str(e2)) for w in wl])) \
            for e1 in [k.left, k.right] if math.isfinite(e1) for e2 in [i.left, i.right] if math.isfinite(e2)])
