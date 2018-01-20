
import itertools
from formula import *
from expr import *


def genVarExpr(initial):
    counter = initial
    while True:
        yield VariableExpr('v' + str(counter))
        counter += 1


def guessPartition(formula, baseSize):
    result = {}
    gen = genVarExpr(0)
    _guessPartition(formula, [next(gen) for _ in range(baseSize)], gen, result)
    return result


def _guessPartition(formula, baseCase, genVar, result):
    if isinstance(formula, Unary):
        _guessPartition(formula.child, baseCase, genVar, result)
    if isinstance(formula, Binary):
        _guessPartition(formula.left,  baseCase, genVar, result)
        _guessPartition(formula.right, baseCase, genVar, result)
    if isinstance(formula, Multiary):
        for c in formula.children:
            _guessPartition(c,  baseCase, genVar, result)

    if isinstance(formula, NotFormula):
        result[formula] = result[formula.child]
    elif isinstance(formula, ConstantFormula):
        result[formula] = []
    elif isinstance(formula, PropositionFormula):
        result[formula] = baseCase
    elif isinstance(formula, Multiary):
        result[formula] = list(itertools.chain.from_iterable([result[c] for c in formula.children]))
    elif isinstance(formula, ImpliesFormula):
        result[formula] = result[formula.left] + result[formula.right]
    elif isinstance(formula, UnaryTemporalFormula):
        csize = len(result[formula.child])
        result[formula] = [next(genVar) for _ in range(2 * (csize + 2))]
    elif isinstance(formula, BinaryTemporalFormula):
        csize = len(result[formula.left]) + len(result[formula.right])
        result[formula] = [next(genVar) for _ in range(2 * (lsize + rsize + 2))]

