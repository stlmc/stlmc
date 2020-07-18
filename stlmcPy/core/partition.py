# import math, itertools
# from .base import genId
# from stlmcPy.constraints.node import *
# from .formula import *
# from .interval import *
# from functools import singledispatch
#
# # We add linear order constraints for separation only
#
# def baseCase(baseSize):
#     genVar = genId(0, "tau_")
#     return [Real(next(genVar)) for _ in range(baseSize)]
#
# # result : partition (key : formula, value : matched partition)
# # sepMap :
# # bConsts : partitionConsts
# def guessPartition(formula, baseCase):
#     result = {}
#     sepMap = {}
#
#     # add order constraints based on base partition (ex . tau_0 < tau_1 ...) to bConst
#     #_addConstOrd(baseCase, genVar, bConst, False)  # change to tau_0 <= tau_1 ...
#     _guess(formula, baseCase, result, sepMap)
#
#     return (result, sepMap)
#
# def genPartition(baseP, sepMap, subFormula):
#     newsubFormula = dict()
#     consts = []
#     consts.extend([Le(baseP[i], baseP[i+1]) for i in range(len(baseP)-1)])
#
#
#     for (k, t) in subFormula.keys():
#         newsubFormula[(k, str(t))] = subFormula[(k,t)]
#
#     subGlobal = dict()
#     for (k,t) in sepMap.keys():
#         subGlobal[k] = (RealVal(float(t.left)), RealVal(float(t.right)))
#
#     subKeys = set()
#     timeInterval = list()
#     if len(baseP) > 0:
#         timeInterval.append(str(Interval(True, 0.0, False, baseP[0])))
#
#     for i in range(len(baseP)):
#         timeInterval.append(str(Interval(True, baseP[i], True, baseP[i])))
#         if i == (len(baseP) -1):
#             timeInterval.append(str(Interval(False, baseP[i], False, float('inf'))))
#         else:
#             timeInterval.append(str(Interval(False, baseP[i], False, baseP[i+1])))
#
#     for (k, t) in newsubFormula.keys():
#         subKeys.add(k)
#
#     propOrdDict = dict()
#     for k in subKeys:
#         subList = []
#         for t in timeInterval:
#             if (k, t) in newsubFormula.keys():
#                 subList.append(newsubFormula[(k,t)][0])
#         propOrdDict[k] = subList
#
#     baseP.insert(0, RealVal(0))
#
#     for k in propOrdDict.keys():
#         left = subGlobal[k][0]
#         right = subGlobal[k][1]
#         for i in range(1, len(baseP)):
#             sub = []
#             sub.append(Not(Beq(propOrdDict[k][2 * i -2],propOrdDict[k][2 * i -1])))
#             sub.append(Not(Beq(propOrdDict[k][2 * i -1],propOrdDict[k][2 * i])))
#             subLeft = []
#             subRight = []
#             for j in range(0, i):
#                 subLeft.append(Implies((baseP[i] - left) >= RealVal(0), Numeq((baseP[i] - left), baseP[j])))
#                 subRight.append(Implies((baseP[i] - right) >= RealVal(0), Numeq((baseP[i] -right), baseP[j])))
#             consts.append(Implies(Or(*sub), And(Or(*subLeft), Or(*subRight))))
#
#     return consts
#
# @singledispatch
# def _guess(formula, baseCase, result, sepMap):
#     raise NotImplementedError('Something wrong')
#
# @_guess.register(ConstantFormula)
# def _(formula, baseCase, result, sepMap):
#     result[formula] = set()
#
# @_guess.register(PropositionFormula)
# def _(formula, baseCase, result, sepMap):
#     result[formula] = set(baseCase)
#
# @_guess.register(NotFormula)
# def _(formula, baseCase, result, sepMap):
#     _guess(formula.child, baseCase, result, sepMap)
#     # result[formula] = result[formula.child]
#     result[formula] = set(baseCase)
#
# @_guess.register(Multiary)
# def _(formula, baseCase, result, sepMap):
#     for c in formula.children:
#         _guess(c,  baseCase, result, sepMap)
#     # result[formula] = set(itertools.chain.from_iterable([result[c] for c in formula.children]))
#     result[formula] = set(baseCase)
#
# @_guess.register(ImpliesFormula)
# def _(formula, baseCase, result, sepMap):
#     _guess(formula.left,  baseCase, result, sepMap)
#     _guess(formula.right, baseCase, result, sepMap)
#     # result[formula] = result[formula.left] | result[formula.right]
#     result[formula] = set(baseCase)
#
#
# @_guess.register(UnaryTemporalFormula)
# def _(formula, baseCase, result, sepMap):
#     _guess(formula.child, baseCase, result, sepMap)
#
#     p = result[formula.child]
#     # sepMap[formula] = [Real(next(genVar)) for _ in range(len(p))]
#     sepMap[formula] = baseCase
#
#     # result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}
#     result[formula] = set(baseCase)
#
#     #_addConstOrd(sepMap[formula])
#     #_addConstEqu(sepMap[formula], p)
#
#
#
#     # _addConstPar(result[formula], p, formula.gtime, formula.ltime)
#
#
# @_guess.register(BinaryTemporalFormula)
# def _(formula, baseCase, result, sepMap):
#     _guess(formula.left,  baseCase, result, sepMap)
#     _guess(formula.right, baseCase, result, sepMap)
#
#     p = result[formula.left] | result[formula.right]
#     # sepMap[formula] = [Real(next(genVar)) for _ in range(len(p))]
#     sepMap[formula] = baseCase
#
#     # result[formula] = {Real(next(genVar)) for _ in range(2 * (len(p) + 2))}
#     result[formula] = set(baseCase)
#
#     # _addConstOrd(sepMap[formula], genVar)
#     # _addConstEqu(sepMap[formula], p)
#
#
#
#     # _addConstPar(result[formula], p, formula.gtime, formula.ltime)
#
#
# def _addConstOrd(bCase, genVar, bConst, strict=False):
#     op = ArithRef.__lt__ if strict else ArithRef.__le__
#     bConst.extend([op(bCase[i], bCase[i+1]) for i in range(len(bCase)-1)])
#
#
# def _addConstEqu(wl, yl, const):
#     for w in wl:
#         const.append(Or(*[w == y for y in yl]))
#     for y in yl:
#         const.append(Or(*[y == w for w in wl]))
#
# # result[formula], result[formula.child], formula.gtime, formula.ltime, const)
# def _addConstPar(wl, yl, k:Interval, i:Interval, const):
#     def _constEnd(w, y):
#         arg = [w == RealVal(0)] + [w == y - RealVal(e) for e in [i.left,i.right] if math.isfinite(e)]
#         return Or(*arg)
#     for w in wl:
#         arg = [And(inInterval(y, k), _constEnd(w, y)) for y in yl] + [_constEnd(w, RealVal(e)) for e in [k.left, k.right] if math.isfinite(e)]
#         const.append(Or(*arg))
#         const.append(w >= RealVal(0))
#     const.extend([Implies(And(inInterval(y,k), y - RealVal(e) >= RealVal(0)), Or(*[w == y - RealVal(e) for w in wl])) \
#             for y in yl for e in [i.left, i.right] if math.isfinite(e)])
#     const.extend([Implies(RealVal(e1) - RealVal(e2) >= RealVal(0), Or(*[w == RealVal(e1) - RealVal(e2) for w in wl])) \
#             for e1 in [k.left, k.right] if math.isfinite(e1) for e2 in [i.left, i.right] if math.isfinite(e2)])
