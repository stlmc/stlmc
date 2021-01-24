import itertools
import math
from functools import singledispatch

# We add linear order constraints for separation only
from stlmcPy.constraints.interval import inInterval
from stlmcPy.constraints.operations import generate_id
from stlmcPy.constraints.constraints import *


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
    sepMap[formula] = list(p)

    result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}

    _addConstOrd(sepMap[formula], genVar, const)
    # _addConstEqu(sepMap[formula], p, const)
    _addConstPar(result[formula], p, formula.global_time, formula.local_time, const)


@_guess.register(BinaryTemporalFormula)
def _(formula, baseCase, genVar, result, sepMap, const):
    _guess(formula.left, baseCase, genVar, result, sepMap, const)
    _guess(formula.right, baseCase, genVar, result, sepMap, const)

    p = result[formula.left] | result[formula.right]
    sepMap[formula] = list(p)

    result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}

    _addConstOrd(sepMap[formula], genVar, const)
    # _addConstEqu(sepMap[formula], p, const)
    _addConstPar(result[formula], p, formula.global_time, formula.local_time, const)


def _addConstOrd(bCase, genVar, bConst, strict=False):
    # op = ArithRef.__lt__ if strict else ArithRef.__le__
    if strict:
        bConst.extend([Lt(bCase[i], bCase[i + 1]) for i in range(len(bCase) - 1)])
    else:
        bConst.extend([Leq(bCase[i], bCase[i + 1]) for i in range(len(bCase) - 1)])


def _addConstEqu(wl, yl, const):
    for w in wl:
        const.append(Or([w == y for y in yl]))
    for y in yl:
        const.append(Or([y == w for w in wl]))


# result[formula], result[formula.child], formula.gtime, formula.ltime, const)
def _addConstPar(wl, yl, k: Interval, i: Interval, const):
    def _constEnd(w, y):
        arg = [w == RealVal("0")] + [Implies(Geq(y - RealVal(str(e)), RealVal("0")), w == y - RealVal(str(e))) for e in
                                     [i.left, i.right] if math.isfinite(e)]
        return Or(arg)

    all_vars_list = list(wl)
    all_vars_list = sorted(all_vars_list, key=lambda x: int(x.id[8:]))
    for w in range(len(all_vars_list) - 1):
        const.append(all_vars_list[w] <= all_vars_list[w + 1])
    for w in all_vars_list:
        arg_list = list()
        arg_list.append(Eq(w, RealVal("0")))
        for y in yl:
            for e in [i.left, i.right]:
                if math.isfinite(e):
                    arg_list.extend(
                        [And([inInterval(y, k), y - RealVal(str(e)) >= RealVal("0"), w == y - RealVal(str(e))])])

        const.append(Or(arg_list))
    for w in all_vars_list:
        for y in yl:
            const.append(_constEnd(w, y))
    for y in yl:
        for e in [i.left, i.right]:
            arg_list = list()
            if math.isfinite(e):
                for w in all_vars_list:
                    arg_list.append(Eq(w, y - RealVal(str(e))))
                const.append(Implies(Geq(y - RealVal(str(e)), RealVal("0")), Or(arg_list)))

    const.extend([Implies(And([inInterval(y, k), y - RealVal(str(e)) >= RealVal("0")]),
                          Or([w == y - RealVal(str(e)) for w in wl])) \
                  for y in yl for e in [i.left, i.right] if math.isfinite(e)])
