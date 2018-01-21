
import itertools
import z3
from base import genId
from formula import *
from functools import singledispatch


def guessPartition(formula, baseSize):
    result = {}
    genVar = genId(0)

    (bCase,bConst) = _genVar(baseSize, genVar)

    print (bConst)

    _guess(formula, bCase, genVar, result, bConst)
    return result


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
    csize = len(result[formula.child])
    result[formula] = [z3.Real(next(genVar)) for _ in range(2 * (csize + 2))]

@_guess.register(BinaryTemporalFormula)
def _(formula, baseCase, genVar, result, const):
    _guess(formula.left,  baseCase, genVar, result, const)
    _guess(formula.right, baseCase, genVar, result, const)
    csize = len(result[formula.left]) + len(result[formula.right])
    result[formula] = [z3.Real(next(genVar)) for _ in range(2 * (csize + 2))]


def _genVar(size, genVar):
    bCase = [z3.Real(next(genVar)) for _ in range(size)]
    return (bCase, z3.And([bCase[i] <= bCase[i+1] for i in range(size-1)])) 


def _genConst(wl, yl, k, l, r):
    for w in wl:
        for y in yl:
            pass
