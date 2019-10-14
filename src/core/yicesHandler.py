from yices import *
import itertools
from functools import singledispatch
from .error import *
from .node import *


# return a check result and the Z3 constraint size
def checkSat(consts, logic="None"):
    yicesConsts=[yicesObj(c) for c in consts]
    if logic != "None":
        solver = yices.SolverFor(logic)
    else:
        solver = yices.Solver()
    
#    target_yices_simplify = yices.simplify(yices.And(*yicesConsts))
#    solver.add(target_yices_simplify)

    solver.add(yicesConsts)

    solver.set("timeout", 9000000)  #timeout : 150 min
    with open("thermoLinear.smt2", 'w') as fle:
        print(solver.to_smt2(), file=fle)

    result = solver.check()
    if result == yices.sat:
        m = solver.model()
    else:
        m = None

    return (result, sizeAst(yices.And(*yicesConsts)), m)

# return the size of the Z3 constraint
def sizeAst(node:yices.AstRef):
    return 1 + sum([sizeAst(c) for c in node.children()])


@singledispatch
def yicesObj(const:Node):
    raise NotImplementedError('Something wrong')

@yicesObj.register(Constant)
def _(const):
    op = {Type.Bool: Types.bool_type(), Type.Real: Types.real_type(), Type.Int: Types.int_type()}
    if const.getType() == Type.Bool:
        value = Terms.TRUE if const.value else Terms.FALSE
        return value
    else:
        value = str(const.value)
    return Terms.constant(op[const.getType()], value)

@yicesObj.register(Variable)
def _(const):
    op = {Type.Bool: Types.bool_type(), Type.Real: Types.real_type(), Type.Int: Types.int_type()}
    return  Terms.new_uninterpreted_term(op[const.getType()], str(const.id))

@yicesObj.register(Ge)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.arith_geq_atom(x, y)

@yicesObj.register(Gt)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.arith_gt_atom(x, y)

@yicesObj.register(Le)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.arith_leq_atom(x, y)

@yicesObj.register(Lt)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.arith_lt_atom(x, y)

@yicesObj.register(Numeq)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.arith_eq_atom(x, y)

@yicesObj.register(Plus)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.add(x, y)

@yicesObj.register(Minus)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.sub(x, y)

@yicesObj.register(Pow)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.power(x, y)

@yicesObj.register(Mul)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.mul(x, y)

@yicesObj.register(Div)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Temrs.division(x, y)

@yicesObj.register(Neg)
def _(const):
    x = yicesObj(const.child())
    return Terms.neg(x)

@yicesObj.register(And)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return True
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        return yices.And(yicesargs)

@yicesObj.register(Or)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return True
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        return yices.Or(yicesargs)

@yicesObj.register(Implies)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return yices.Implies(x, y)

@yicesObj.register(Beq)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return x == y

@yicesObj.register(Not)
def _(const):
    x = yicesObj(const.child())
    return yices.Not(x)

@yicesObj.register(Integral)
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
                        raise yicesconstODEerror()
        substitutionExp = {}
        for i in const.ode.keys():
            substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_') 
            keyValue = str(const.endList[i])[0:keyIndex]
            result.append(const.endList[i] == const.startList[i] + substitutionExp[keyValue] * const.time)
  
    elif const.flowType == 'sol':
        subDict['time'] = const.time
        substitutionExp = {}
        for i in const.ode.keys():
            substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
        for i in range(len(const.endList)):
            keyIndex = str(const.endList[i]).find('_')
            keyValue = str(const.endList[i])[0:keyIndex]
            result.append(const.endList[i] == substitutionExp[keyValue])
    else:
        raise FlowTypeEerror() 


    yicesresult = [yicesObj(c) for c in result]
    return yices.And(yicesresult) 

@yicesObj.register(Forall)
def _(const):
    typeList = [i.getType() for i in const.condition.getVars()]
    if not(Type.Real in typeList):
        subCondition = yicesObj(const.condition.substitution(const.modeDict))
        return subCondition
    else:
        endCond = yicesObj(const.condition.substitution(const.endDict))
        startCond = yicesObj(const.condition.substitution(const.startDict))
        return yices.And(endCond, startCond)

@yicesObj.register(Solution)
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
                    raise yicesconstODEerror()
            else:
                raise yicesconstODEerror()
    substitutionExp = {}
    for i in const.ode.keys():
        substitutionExp[str(i.id)] = const.ode[i].substitution(subDict)
    result = []
    for i in range(len(const.endList)):
        keyIndex = str(const.endList[i]).find('_')
        keyValue = str(const.endList[i])[0:keyIndex]
        result.append(const.endList[i] == substitutionExp[keyValue])

    yicesresult = [yicesObj(c) for c in result]
    return yices.And(yicesresult)

