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

@singledispatch
def clause(const:Node):
    return [const]

@clause.register(And)
def _(const):
    result = list()
    for c in list(const.children):
        result.extend(clause(c))
    return result

@clause.register(Or)
def _(const):
    result = list()
    for c in list(const.children):
        result.extend(clause(c))
    return result

def determine(form, strContVars):
    subVars = list(form.getVars())
    for sv in subVars:
        if isinstance(sv.id, Bool):
            return False
        else:
            strv = str(sv.id)
            vid = strv[0:strv.find('_')]
            if not vid in strContVars:
                return False
    return True

def isGuard(form):
    subVars = list(form.getVars())
    for sv in subVars:
        strv = str(sv.id)
        flag = strv[-1]
        if (flag == '0'):
            return False
    return True

def hylaaModel(consts, contVars, bound, modeModules):
    strContVars = [c.id for c in contVars]

    # Only consider jump constraints
    clist = clause(consts[-1])

    # Delete duplicate items
    clist = list(dict.fromkeys(clist))

    # Delete conditions of mode variables 
    # (Only consider jump conditions of continuous variables)
    clist = [x for x in clist if determine(x, strContVars)]
    
    z3Consts = [z3Obj(c) for c in consts]
    solver = z3.Solver()
    solver.add(z3Consts)

    with open("thermoLinear.smt2", 'w') as fle:
        print(solver.to_smt2(), file=fle)

    result = solver.check()
    z3Jump = list()
    if str(result) == "sat":
        m = solver.model()
        strContVars = [c.id for c in contVars]

        # Only consider jump constraints
        clist = clause(consts[-1])
    
        # Delete duplicate items
        clist = list(dict.fromkeys(clist))
    
        # Delete conditions of mode variables
        # (Only consider jump conditions of continuous variables)
        clist = [x for x in clist if determine(x, strContVars)]
        cguard = [x for x in clist if isGuard(x)]
        creset = [x for x in clist if not isGuard(x)]
        cguard = [x for x in cguard if m.eval(z3Obj(x))]
        creset= [x for x in creset if m.eval(z3Obj(x))]
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

    ha = make_automaton(numModes, modeModules, len(contVars), contVarList, cguard, creset)

    result = False
    cSize = -1
    return (result, cSize)

def getStrInfixExp(exp):
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
    elif exp.op == '<=' or exp.op == '=':
        exp = left + ' - ' + right
        op = True
    return (exp, op)


def make_automaton(numModes, modeModules, numContVars, contVarList, guard, reset):
    ha = HybridAutomaton('Hybrid automata')

    # i is the current bound
    for i in range(len(numModes)):
        m = ha.new_mode('Mode_' + str(i))
        print("current Mode")
        print(numModes[i])
        flowExp = modeModules[int(numModes[i].as_decimal(6).replace("?", ""))].getFlow().exp()
        # Assume no mode variables in invariant
        invExp = modeModules[int(numModes[i].as_decimal(6).replace("?", ""))].getInv()
        leftside = list()
        rightside = list()

        for j in range(len(invExp.props)):
            exp = invExp.props[j]
            (exp, op) = getStrInfixExp(exp)

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

    '''
    m = ha.new_mode('Mode_' + str(len(numModes)))
    flowList = [[0 for x in range(len(contVarList))] for y in range(numContVars * len(numModes) + 1)]
    m.set_dynamics(flowList)
    '''

    for i in range(len(numModes) - 1):
        pre = ha.modes['Mode_' + str(i)]
        post = ha.modes['Mode_' + str(i+1)]
        t = ha.new_transition(pre, post)
        gleft = list()
        gright = list()
        for j in guard:
            j = j.infix()
            if not (str(j).find('=') == -1):
                subleft = [0] * len(contVarList)
            else:
                subleft = [-0.0] * len(contVarList)
            subg = parse_expr(j, evaluate = True)
            coDict = subg.as_coefficients_dict()
            if coDict[1] is not None:
                gright.append(-coDict[1])
            else:
                gright.append(0)
            for p in (coDict.keys()):
                for q in range(i * numContVars, (i + 1) * numContVars):
                    if contVarList[q] == str(p)[0:-2]:
                        subleft[q] = coDict[p]

            gleft.append(subleft)
        t.set_guard(gleft, gright)

        reset_csr = [[0 for x in range(len(contVarList))] for y in range(numContVars)]
        numDeclConsts = 0 
        index = 2
        m_index = list()

        for ri in range(len(reset) - numContVars):
            r = reset[ri]
            sub = [0] * len(contVarList)
            subreset = parse_expr(r.right().infix(), evaluate = True)
            coDict= subreset.as_coefficients_dict()
            constant = 0
            if coDict[1] is not None:
                constant = coDict[1]
                if not str(constant) == '0':
                    numDeclConsts = numDeclConsts + 1
            for p in (coDict.keys()):
                for q in range((i) * numContVars, (i + 1) * numContVars):
                    if contVarList[q] == str(p)[0:-2]:
                        sub[q] = coDict[p]
            m_index.append((index, constant))
            reset_csr.append(sub)
            index = index + 1

        # For constant variable
        sub = [0] * len(contVarList)
        reset_csr.append(sub)

        m_csr = [[0 for x in range(numDeclConsts)] for y in range(len(contVarList))]
        constant = 0
        c_rhs = list()
        for (var_index, constValue) in m_index:
            if not (str(constValue) == '0'):
                m_csr[var_index][constant] = 1
                c_rhs.append(constValue)
                c_rhs.append(-constValue)
                constant = constant + 1
        c_csr = [[0 for x in range(numDeclConsts)] for y in range(numDeclConsts * 2)]
        for ci in range(numDeclConsts):
            c_csr[ci * 2][ci] = 1
            c_csr[ci * 2 + 1][ci] = -1

        t.set_reset(reset_csr, m_csr, c_csr, c_rhs)
    return ha


