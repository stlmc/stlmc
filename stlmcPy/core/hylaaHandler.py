import itertools
from functools import singledispatch
from .model import *
from .node import *
from .z3Handler import *

from matplotlib import collections

from sympy.parsing.sympy_parser import parse_expr

from hylaa.hybrid_automaton import HybridAutomaton
from hylaa.settings import HylaaSettings, PlotSettings, LabelSettings
from hylaa.core import Core
from hylaa.aggstrat import Aggregated
from hylaa.stateset import StateSet
from hylaa import lputil


def hylaaModel(consts, contVars, bound, modeModules):
    z3Consts = [z3Obj(c) for c in consts]
    solver = z3.Solver()
    solver.add(z3Consts)

    result = solver.check()
    if str(result) == "sat":
        m = solver.model()
        print(m)
    else:
        m = None
        raise ("No transition exists")

    numModes = list()
    for i in range(bound + 1):
        modeVar = z3.Real('currentMode_' + str(i))
        numModes.append(m[modeVar])

    contVarList = list()
    for j in range(bound + 1):
        for i in range(len(contVars)):
            contVarList.append(str(contVars[i].id) + "_" + str(j))
    contVarList.append('constant_value')

    make_automaton(numModes, modeModules, len(contVars), contVarList)

    result = False
    cSize = -1
    return (result, cSize)

def make_automaton(numModes, modeModules, numContVars, contVarList):
    ha = HybridAutomaton('Hybrid automata')

    # i is the current bound
    for i in range(len(numModes)):
        m = ha.new_mode('Mode_' + str(i))
        print("current Mode")
        print(numModes[i])
        flowExp = modeModules[int(numModes[i].as_decimal(6).replace("?", ""))].getFlow().exp()
        invExp = modeModules[int(numModes[i].as_decimal(6).replace("?", ""))].getInv()
        leftside = list()
        rightside = list()
        for j in range(len(invExp.props)):
            exp = invExp.props[j]
            if not isinstance(exp.left, str):
                left = str(exp.left.infix())
            else:
                left = exp.left
            if not isinstance(exp.right, str):
                right = str(exp.right.infix())
            else:
                right = exp.right
            if exp.op == '>':
                exp = right + ' - ' + left
                op = False
            elif exp.op == '>=':
                exp = right + ' - ' + left
                op = True
            elif exp.op == '<':
                exp = left + ' - ' + right
                op = False
            elif exp.op == '<=':
                exp = left + ' - ' + right
                op = True

            if op:
                subleft = [0] * len(contVarList)
            else:
                subleft = [-0.0] * len(contVarList)
            inv = parse_expr(str(exp), evaluate = True)
            coDict = inv.as_coefficients_dict()
            if coDict[1] is not None:
                rightside.append(-coDict[1])
            else:
                rightside.append(0)

            for p in (coDict.keys()):
                for q in range(i * numContVars, (i + 1) * numContVars):
                    sliceIndex = contVarList[q].find("_")
                    if contVarList[q][0:sliceIndex] == str(p):
                        subleft[q] = coDict[p]

            leftside.append(subleft)

        flowList = list()
        subFlow = [0] * len(contVarList)
        for j in range(0, i * numContVars):
            flowList.append(subFlow)
        for k in range(len(flowExp)):
            subFlow = list()
            for j in range(i * numContVars, (i + 1) * numContVars): 
                sliceIndex = contVarList[j].find("_")
                if contVarList[j][0:sliceIndex] == flowExp[k].getVarId():
                    flow = parse_expr(flowExp[k].flow.infix(), evaluate = True)
                    coDict = flow.as_coefficients_dict()
                    if len(coDict) == 1:
                        coDict = dict((y,x) for x,y in dict(coDict).items())
                        subFlow = [0] * (len(contVarList) - 1)
                        subFlow.append(coDict[1])
                        flowList.append(subFlow)
                    else:
                        subFlow = [0] * (len(contVarList) - 1)
                        for p in (coDict.keys()):
                            for q in range(i * numContVars, (i + 1) * numContVars):
                                if contVarList[q][0:sliceIndex] == str(p):
                                    subFlow[q] = coDict[p] 

                        if coDict[1] is not None:
                            subFlow.append(coDict[1])
                        else:
                            subFlow.append(0)
                        flowList.append(subFlow)
        subFlow = [0] * len(contVarList)
        for j in range((i+1) * numContVars, len(contVarList)):
            flowList.append(subFlow)

        m.set_dynamics(flowList)
        m.set_invariant(leftside, rightside)




@singledispatch
def hyObj(const:Node):
    print(type(const))
    print(const)
    raise NotImplementedError('Something wrong')

@hyObj.register(Constant)
def _(const):
    op = {Type.Bool: z3.BoolVal, Type.Real: z3.RealVal, Type.Int: z3.IntVal}
    if const.getType() == Type.Bool:
        value = True if const.value else False
    else:
        value = str(const.value)
    return op[const.getType()](value)

@hyObj.register(Variable)
def _(const):
    op = {Type.Bool: z3.Bool, Type.Real: z3.Real, Type.Int: z3.Int}
    return  op[const.getType()](str(const.id))

@hyObj.register(Ge)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x >= y

@hyObj.register(Gt)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x > y

@hyObj.register(Le)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x <= y

@hyObj.register(Lt)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x < y

@hyObj.register(Numeq)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x == y

@hyObj.register(Plus)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x + y

@hyObj.register(Minus)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x - y

@hyObj.register(Pow)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x**y

@hyObj.register(Mul)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x * y

@hyObj.register(Div)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x / y

@hyObj.register(Neg)
def _(const):
    x = hyObj(const.child())
    return -x

@hyObj.register(And)
def _(const):
    z3args = [hyObj(c) for c in const.children]
    if len(z3args) < 1:
        return True
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.And(z3args)

@hyObj.register(Or)
def _(const):
    z3args = [hyObj(c) for c in const.children]
    if len(z3args) < 1:
        return True
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.Or(z3args)

@hyObj.register(Implies)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return z3.Implies(x, y)

@hyObj.register(Beq)
def _(const):
    x = hyObj(const.left())
    y = hyObj(const.right())
    return x == y

@hyObj.register(Not)
def _(const):
    x = hyObj(const.child())
    return z3.Not(x)

@hyObj.register(Integral)
def _(const):
    result = const.getConstraints()
    z3result = [hyObj(c) for c in result]
    return z3.And(z3result) 

@hyObj.register(Forall)
def _(const):
    result = getForallConsts(const)
    z3result = [hyObj(c) for c in result]
    return z3.And(z3result)

@hyObj.register(Solution)
def _(const):
    result = const.getConstraints()
    z3result = [hyObj(c) for c in result]
    return z3.And(z3result)


