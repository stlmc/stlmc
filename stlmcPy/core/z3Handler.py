import z3
import itertools
from functools import singledispatch
from .error import *
from .node import *


# return a check result and the Z3 constraint size
def z3checkSat(consts, logic):
    z3Consts=[z3Obj(c) for c in consts]

    if logic != "NONE":
        solver = z3.SolverFor(logic)
    else:
        solver = z3.Solver()

    # solver.set("timeout", timeout * 1000)
    target_z3_simplify = z3.simplify(z3.And(*z3Consts))
    solver.add(target_z3_simplify)

    result = solver.check()
    str_result = str(result)
    if str_result == "sat":
        m = solver.model()
        result = False
    else:
        m = None
        result = True if str_result == "unsat" else "Unknown"
    return (result, sizeAst(z3.And(*z3Consts)), m)

# return the size of the Z3 constraint
def sizeAst(node:z3.AstRef):
    return 1 + sum([sizeAst(c) for c in node.children()])


@singledispatch
def z3Obj(const:Node):
    print(type(const))
    print(const)
    raise NotImplementedError('Something wrong')

@z3Obj.register(Constant)
def _(const):
    op = {Type.Bool: z3.BoolVal, Type.Real: z3.RealVal, Type.Int: z3.IntVal}
    if const.getType() == Type.Bool:
        value = True if const.value else False
    else:
        value = str(const.value)
    return op[const.getType()](value)

@z3Obj.register(Variable)
def _(const):
    op = {Type.Bool: z3.Bool, Type.Real: z3.Real, Type.Int: z3.Int}
    return  op[const.getType()](str(const.id))

@z3Obj.register(Ge)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x >= y

@z3Obj.register(Gt)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x > y

@z3Obj.register(Le)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x <= y

@z3Obj.register(Lt)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x < y

@z3Obj.register(Numeq)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x == y

@z3Obj.register(Plus)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x + y

@z3Obj.register(Minus)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x - y

@z3Obj.register(Pow)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x**y

@z3Obj.register(Mul)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x * y

@z3Obj.register(Div)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x / y

@z3Obj.register(Neg)
def _(const):
    x = z3Obj(const.child())
    return -x

@z3Obj.register(And)
def _(const):
    z3args = [z3Obj(c) for c in const.children]
    if len(z3args) < 1:
        return True
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.And(z3args)

@z3Obj.register(Or)
def _(const):
    z3args = [z3Obj(c) for c in const.children]
    if len(z3args) < 1:
        return True
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.Or(z3args)

@z3Obj.register(Implies)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return z3.Implies(x, y)

@z3Obj.register(Beq)
def _(const):
    x = z3Obj(const.left())
    y = z3Obj(const.right())
    return x == y

@z3Obj.register(Not)
def _(const):
    x = z3Obj(const.child())
    return z3.Not(x)

@z3Obj.register(Integral)
def _(const):
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
                        raise z3constODEerror()
        substitutionExp = {}
        for i in const.ode.keys():
            substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_') 
            keyValue = str(const.endList[i])[0:keyIndex]
            if keyValue in substitutionExp.keys():
                result.append(const.endList[i] == const.startList[i] + substitutionExp[keyValue] * const.time)
  
    elif const.flowType == 'sol':
        subDict['time'] = Real('tau_' + str(const.time.id)[4:])
        substitutionExp = {}
        for i in const.ode.keys():
            substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_')
            keyValue = str(const.endList[i])[0:keyIndex]
            if keyValue in substitutionExp.keys():
                result.append(const.endList[i] == substitutionExp[keyValue])
    else:
        raise FlowTypeEerror() 


    z3result = [z3Obj(c) for c in result]
    return z3.And(z3result) 

@z3Obj.register(Forall)
def _(const):
    typeList = [i.getType() for i in const.condition.getVars()]
    if not(Type.Real in typeList):
        subCondition = z3Obj(const.condition.substitution(const.modeDict))
        return subCondition
    else:
        endCond = z3Obj(const.condition.substitution(const.endDict))
        startCond = z3Obj(const.condition.substitution(const.startDict))
        return z3.And(endCond, startCond)

@z3Obj.register(Solution)
def _(const):
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
                    raise z3constODEerror()
            else:
                raise z3constODEerror()
    substitutionExp = {}
    for i in const.ode.keys():
        substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
    result = []
    for i in range(len(const.endList)):
        keyIndex = str(const.endList[i]).find('_')
        keyValue = str(const.endList[i])[0:keyIndex]
        result.append(const.endList[i] == substitutionExp[keyValue])

    z3result = [z3Obj(c) for c in result]
    return z3.And(z3result)

