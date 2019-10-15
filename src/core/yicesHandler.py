from yices import *
import yices_api as yapi
import itertools
from functools import singledispatch
from .error import *
from .node import *


# return a check result and the Z3 constraint size
def yicescheckSat(consts, logic="None"):
    yicesConsts=[yicesObj(c) for c in consts]
    cfg = Config()

    if logic != "None":
        cfg.default_config_for_logic(logic)
    else:
        cfg.default_config_for_logic('QF_NRA')

    ctx = Context(cfg)
    
    ctx.assert_formulas(yicesConsts)

    result = ctx.check_context()
    if result == Status.SAT:
        m = Model.from_context(ctx, 1)
        model_string = m.to_string(80, 100, 0)
        print(model_string)
    else:
        m = None

    cfg.dispose()
    ctx.dispose()
    Yices.exit()

    #return (result, sizeAst(yices.yand(*yicesConsts)), m)
    return (result, -1, m)

'''
# return the size of the Z3 constraint
def sizeAst(node:yices.AstRef):
    #return 1 + sum([sizeAst(c) for c in node.children()])
    return -1
'''

@singledispatch
def yicesObj(const:Node):
    raise NotImplementedError('Something wrong')

@yicesObj.register(Constant)
def _(const):
    if const.getType() == Type.Bool:
        value = Terms.TRUE if const.value else Terms.FALSE
        return value
    if const.getType() == Type.Real:
        return yapi.yices_parse_float(str(const.value))
    if const.getType() == Type.Int:
        return Terms.integer(int(str(const.value)))

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
    return Terms.yand(yicesargs)

@yicesObj.register(Or)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    return Terms.yor(yicesargs)

@yicesObj.register(Implies)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.implies(x, y)

@yicesObj.register(Beq)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    return Terms.eq(x, y)

@yicesObj.register(Not)
def _(const):
    x = yicesObj(const.child())
    return Terms.ynot(x)

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
    return Terms.yand(yicesresult) 

@yicesObj.register(Forall)
def _(const):
    typeList = [i.getType() for i in const.condition.getVars()]
    if not(Type.Real in typeList):
        subCondition = yicesObj(const.condition.substitution(const.modeDict))
        return subCondition
    else:
        endCond = yicesObj(const.condition.substitution(const.endDict))
        startCond = yicesObj(const.condition.substitution(const.startDict))
        return Terms.yand(endCond, startCond)

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
    return Terms.yand(yicesresult)

