from dreal import Variable as drealVar
import itertools
from functools import singledispatch
from .node import *
from .error import *

# return dictionary of declared terms, key : string id, value : dreal object
def drealTerms(consts):
    results = dict()

    for c in consts:
        print(c)
        results = drealDeclared(c, results)

    return results


@singledispatch
def drealDeclared(const:Node, termDict):
    print(type(const))
    print(const)
    raise NotImplementedError('Something wrong')

@drealDeclared.register(Constant)
def _(const, termDict):
    return termDict

@drealDeclared.register(Variable)
def _(const, termDict):
    print("Variable out")
    op = {Type.Bool: drealVar.Bool, Type.Real: drealVar.Real, Type.Int: drealVar.Int}
    print("variable mid")
    print(termDict.keys())
    print("variable mid2")

    if not (str(const.id) in termDict.keys()):
        print("variable")
        print(type(const))
        print(const)
        termDict[str(const.id)] = Variable(str(const.id), op[const.getType()])
        print("after")

    print("varialbe end")
    return termDict

@drealDeclared.register(Ge)
def _(const, termDict):
    print("Ge")
    x = drealDeclared(const.left(), termDict)
    print(x)
    y = drealDeclared(const.right(), x)
    print(y)
    print("Gt end")
    return y

@drealDeclared.register(Gt)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Le)
def _(const, termDict):
    print("LE")
    print(termDict)
    print(type(const.left()))
    x = drealDeclared(const.left(), termDict)
    print("mid")
    y = drealDeclared(const.right(), x)
    print("end")
    return y

@drealDeclared.register(Lt)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Numeq)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Plus)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Minus)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Pow)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Mul)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Div)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Neg)
def _(const, termDict):
    x = drealDeclared(const.child(), termDict)
   
    return x

@drealDeclared.register(And)
def _(const, termDict):
    for i in const.children:
        print(i)
        termDict = drealDeclared(i, termDict)

    return termDict

@drealDeclared.register(Or)
def _(const, termDict):
    for i in const.children:
        termDict = drealDeclared(i, termDict)

    return termDict

@drealDeclared.register(Implies)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Beq)
def _(const, termDict):
    x = drealDeclared(const.left(), termDict)
    y = drealDeclared(const.right(), x)
    return y

@drealDeclared.register(Not)
def _(const, termDict):
    x = drealDeclared(const.child(), termDict)
    return x

@drealDeclared.register(Integral)
def _(const, termDict):
    print("Integral")
    result = []
    subDict = {}
    for i in range(len(const.endList)):
        keyIndex = str(const.endList[i]).find('_')
        keyValue = str(const.endList[i])[0:keyIndex]
        subDict[keyValue] = const.startList[i]
    if const.flowType == 'diff':
        for i in const.ode.values():
            subvariables = list(i.getVars())
            for j in range(len(subvariables)):
                if subvariables[j] in const.ode.keys():
                    if str(const.ode[subvariables[j]]) == str(RealVal(0)):
                        pass
                    else:
                        print(str(const.ode[subvariables[j]]))
                        raise error.yicesconstODEerror()
        substitutionExp = {}
        for i in const.ode.keys():
            substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_')
            keyValue = str(const.endList[i])[0:keyIndex]
            if keyValue in substitutionExp.keys():
                result.append(const.endList[i] == const.startList[i] + substitutionExp[keyValue] * const.time)

    elif const.flowType == 'sol':
        subDict['time'] = const.time
        substitutionExp = {}
        for i in const.ode.keys():
            substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_')
            keyValue = str(const.endList[i])[0:keyIndex]
            if keyValue in substitutionExp.keys():
                result.append(const.endList[i] == substitutionExp[keyValue])
    else:
        raise error.FlowTypeEerror()

    for c in result:
        termDict = drealDeclared(c, termDict)

    return termDict


@drealDeclared.register(Forall)
def _(const, termDict):
    print("Forall")
    typeList = [i.getType() for i in const.condition.getVars()]
    if not(Type.Real in typeList):
        termDict = drealDeclared(const.condition.substitution(const.modeDict), termDict)
        return termDict
    else:
        endCond = drealDeclared(const.condition.substitution(const.endDict), termDict)
        startCond = drealDeclared(const.condition.substitution(const.startDict), endCond)
        return startCond

@drealDeclared.register(Solution)
def _(const, termDict):
    print("Solution")
    subDict = {}
    for i in range(len(const.endList)):
        keyIndex = str(const.endList[i]).find('_')
        keyValue = str(const.endList[i])[0:keyIndex]
        subDict[keyValue] = const.startList[i]
    for i in const.ode.values():
        subvariables = list(i.getVars())
        for j in range(len(subvariables)):
            if subvariables[j] in const.ode.keys():
                if str(const.ode[subvariables[j]]) == str(RealVal(0)):
                    pass
                else:
                    raise error.yicesconstODEerror()
            else:
                raise error.yicesconstODEerror()
    substitutionExp = {}
    for i in const.ode.keys():
        substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
    result = []
    for i in range(len(const.endList)):
        keyIndex = str(const.endList[i]).find('_')
        keyValue = str(const.endList[i])[0:keyIndex]
        result.append(const.endList[i] == substitutionExp[keyValue])

    for c in result:
        termDict = drealTerms(c, termDict)

    return termDict

