from .constraints import *
from .operations import generate_id
from functools import singledispatch


# We add linear order constraints for separation only

def baseCase(baseSize):
    genVar = generate_id(1, "tau_")
    return [Real(next(genVar)) for _ in range(baseSize)]


# result : partition (key : formula, value : matched partition)
# sepMap :
# bConsts : partitionConsts
def guessPartition(formula, baseCase):
    result = {}
    sepMap = {}

    # add order constraints based on base partition (ex . tau_0 < tau_1 ...) to bConst
    # _addConstOrd(baseCase, genVar, bConst, False)  # change to tau_0 <= tau_1 ...
    _guess(formula, baseCase, result, sepMap)

    return (result, sepMap)


def genPartition(baseP, sepMap, subFormula):
    newsubFormula = dict()
    consts = []
    consts.extend([Leq(baseP[i], baseP[i + 1]) for i in range(len(baseP) - 1)])

    for (k, t) in subFormula.keys():
        newsubFormula[(k, str(t))] = subFormula[(k, t)]

    subGlobal = dict()
    for (k, t) in sepMap.keys():
        subGlobal[k] = (RealVal(float(t.left)), RealVal(float(t.right)))

    subKeys = set()
    timeInterval = list()
    if len(baseP) > 0:
        timeInterval.append(str(Interval(True, 0.0, False, baseP[0])))

    for i in range(len(baseP)):
        timeInterval.append(str(Interval(True, baseP[i], True, baseP[i])))
        if i == (len(baseP) - 1):
            timeInterval.append(str(Interval(False, baseP[i], False, float('inf'))))
        else:
            timeInterval.append(str(Interval(False, baseP[i], False, baseP[i + 1])))

    for (k, t) in newsubFormula.keys():
        subKeys.add(k)

    propOrdDict = dict()
    for k in subKeys:
        subList = []
        for t in timeInterval:
            if (k, t) in newsubFormula.keys():
                subList.append(newsubFormula[(k, t)][0])
        propOrdDict[k] = subList

    baseP.insert(0, RealVal(0))

    for k in propOrdDict.keys():
        left = subGlobal[k][0]
        right = subGlobal[k][1]
        for i in range(1, len(baseP)):
            sub = []
            sub.append(Not(Neq(propOrdDict[k][2 * i - 2], propOrdDict[k][2 * i - 1])))
            sub.append(Not(Neq(propOrdDict[k][2 * i - 1], propOrdDict[k][2 * i])))
            subLeft = []
            subRight = []
            for j in range(0, i):
                subLeft.append(Implies((baseP[i] - left) >= RealVal(0), Eq((baseP[i] - left), baseP[j])))
                subRight.append(Implies((baseP[i] - right) >= RealVal(0), Eq((baseP[i] - right), baseP[j])))
            consts.append(Implies(Or(sub), And([Or(subLeft), Or(subRight)])))

    return consts


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
    # result[formula] = result[formula.child]
    result[formula] = set(baseCase)


@_guess.register(MultinaryFormula)
def _(formula, baseCase, result, sepMap):
    for c in formula.children:
        _guess(c, baseCase, result, sepMap)
    # result[formula] = set(itertools.chain.from_iterable([result[c] for c in formula.children]))
    result[formula] = set(baseCase)


@_guess.register(Implies)
def _(formula, baseCase, result, sepMap):
    _guess(formula.left, baseCase, result, sepMap)
    _guess(formula.right, baseCase, result, sepMap)
    # result[formula] = result[formula.left] | result[formula.right]
    result[formula] = set(baseCase)


@_guess.register(UnaryTemporalFormula)
def _(formula, baseCase, result, sepMap):
    _guess(formula.child, baseCase, result, sepMap)

    p = result[formula.child]
    # sepMap[formula] = [Real(next(genVar)) for _ in range(len(p))]
    sepMap[formula] = baseCase

    # result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}
    result[formula] = set(baseCase)


@_guess.register(BinaryTemporalFormula)
def _(formula, baseCase, result, sepMap):
    _guess(formula.left, baseCase, result, sepMap)
    _guess(formula.right, baseCase, result, sepMap)

    p = result[formula.left] | result[formula.right]
    # sepMap[formula] = [Real(next(genVar)) for _ in range(len(p))]
    sepMap[formula] = baseCase

    # result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}
    result[formula] = set(baseCase)

