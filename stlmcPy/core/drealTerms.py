from dreal import Variable as drealVar
from functools import singledispatch
from .node import *
from .error import *

# return dictionary of declared terms, key : string id, value : dreal object
def drealDeclared(consts):
    results = dict()

    for c in consts:
        results = drealTerms(c, results)

    return results


@singledispatch
def drealTerms(const:Node, declDict):
    print(type(const))
    print(const)
    raise NotImplementedError('Something wrong')

@drealTerms.register(Constant)
def _(const, declDict):
    return declDict

@drealTerms.register(Variable)
def _(const, declDict):
    op = {Type.Bool: drealVar.Bool, Type.Real: drealVar.Real, Type.Int: drealVar.Int}
    if not (str(const.id) in declDict.keys()):
        declDict[str(const.id)] = drealVar(str(const.id), op[const.getType()])
    return declDict 

@drealTerms.register(BinaryArithmetic)
def _(const, declDict):
    x = drealTerms(const.left(), declDict)
    y = drealTerms(const.right(), x)
  
    return y

@drealTerms.register(Beq)
def _(const, declDict):
    x = drealTerms(const.left(), declDict)
    y = drealTerms(const.right(), x)

    return y

@drealTerms.register(Implies)
def _(const, declDict):
    x = drealTerms(const.left(), declDict)
    y = drealTerms(const.right(), x)

    return y

@drealTerms.register(UnaryArithmetic)
def _(const, declDict):
    x = drealTerms(const.child(), declDict)
    return x

@drealTerms.register(Not)
def _(const, declDict):
    x = drealTerms(const.child(), declDict)
    return x

@drealTerms.register(Relational)
def _(const, declDict):
    x = drealTerms(const.left(), declDict)
    y = drealTerms(const.right(), x)

    return y

@drealTerms.register(And)
def _(const, declDict):
    for i in const.children:
        declDict = drealTerms(i, declDict)

    return declDict

@drealTerms.register(Or)
def _(const, declDict):
    for i in const.children:
        declDict = drealTerms(i, declDict)

    return declDict

@drealTerms.register(Integral)
def _(const, declDict):
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
                        raise error.drealconstODEerror()
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
        declDict = drealTerms(c, declDict)

    return declDict

@drealTerms.register(Forall)
def _(const, declDict):
    exp = const.exp
    if isinstance(exp, Lt):
        exp = Gt((exp.right() - exp.left()), RealVal(0))
    if isinstance(exp, Le):
        exp = Ge((exp.right() - exp.left()), RealVal(0))

    # If proposition is just boolean variable, return original expression
    if not (isinstance(exp, Gt) or isinstance(exp, Numeq) or isinstance(exp, Numneq) or isinstance(exp, Ge)):
        if exp.getType() == Type.Bool:
            declDict = drealTerms(exp.substitution(const.modePropDict), declDict) 
            return declDict
        else:
            print(exp)
            print(exp.getType())
            raise ("Proposition constraints something wrong")
    # Case Real value >(or >=) 0
    if len(exp.getVars()) == 0:
        return declDict

    handlingExp = exp.left() - exp.right()
    handlingExp = handlingExp.substitution(const.modePropDict)
    declDict = drealTerms(handlingExp, declDict)
    return declDict 

@drealTerms.register(Solution)
def _(const, declDict):
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
                    raise error.drealconstODEerror()
            else:
                raise error.drealconstODEerror()
    substitutionExp = {}
    for i in const.ode.keys():
        substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
    result = []
    for i in range(len(const.endList)):
        keyIndex = str(const.endList[i]).find('_')
        keyValue = str(const.endList[i])[0:keyIndex]
        result.append(const.endList[i] == substitutionExp[keyValue])

    for c in result:
        declDict = drealTerms(c, declDict)

    return declDict


