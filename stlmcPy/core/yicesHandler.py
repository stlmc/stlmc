from yices import *
import yices_api as yapi
import itertools
import importlib
from functools import singledispatch
from .node import *
from .error import *

def getvarval(self):
    all_terms = self.model.collect_defined_terms()
    var_val = dict()
    for term in all_terms:
        var_val[str(Terms.get_name(term))] = self.model.get_value(term)
    return var_val

# return a check result and the Z3 constraint size
def yicescheckSat(consts, logic):
    strConsts = [yicesObj(c) for c in consts]
    cfg = Config()

    if logic != "NONE":
        cfg.default_config_for_logic(logic)
    else:
        cfg.default_config_for_logic('QF_NRA')

    ctx = Context(cfg)

    yicesConsts = [Terms.parse_term(c) for c in strConsts]

    ctx.assert_formulas(yicesConsts)

    result = ctx.check_context()
    if result == Status.SAT:
        m = Model.from_context(ctx, 1)
        result = False
    else:
        m = None
        result = True if Status.UNSAT else "Unknown"

    cfg.dispose()
    ctx.dispose()

    return (result, sizeAst(Terms.yand(yicesConsts)), m)

# return the size of the Z3 constraint
def sizeAst(node:Terms):
    if node == Terms.NULL_TERM:
        return 0
    retval = yapi.yices_term_num_children(node)
    if retval == -1:
        return 0
    else:
        return 1 + sum([sizeAst(yapi.yices_term_child(node, c)) for c in range(retval)])


@singledispatch
def yicesObj(const:Node):
    print(type(const))
    print(const)
    raise NotImplementedError('Something wrong')

@yicesObj.register(Constant)
def _(const):
    if const.getType() == Type.Bool:
        value = 'true' if const.value else 'false'
        return value
    return str(const.value)

@yicesObj.register(Variable)
def _(const):
    op = {Type.Bool: Types.bool_type(), Type.Real: Types.real_type(), Type.Int: Types.int_type()}
    x = Terms.new_uninterpreted_term(op[const.getType()], str(const.id))

    return  str(const.id)

@yicesObj.register(Ge)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(>= ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Gt)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(> ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Le)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(<= ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Lt)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(< ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Numeq)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(= ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Plus)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(+ ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Minus)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(- ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Pow)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())

    cfg = Config()
    cfg.default_config_for_logic('QF_LRA')
    ctx = Context(cfg)
    red_val = Terms.new_uninterpreted_term(Types.real_type(), 'red')
    red = Terms.parse_term('(= red ' + y + ')')
    ctx.assert_formulas([red])
    status = ctx.check_context()

    if status == Status.SAT:
        model = Model.from_context(ctx, 1)
        yval = str(model.get_value(red_val))
    else:
        raise error.Exception("something wrong in divisor of power")
    cfg.dispose()
    ctx.dispose()
    result = '(^ ' + x + ' ' + yval + ')'
    return result

@yicesObj.register(Mul)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(* ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Div)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(/ ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Neg)
def _(const):
    x = yicesObj(const.child())
    result = '(- ' + str(0) + ' ' + x + ')'
    return result

@yicesObj.register(And)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(and ' + ' '.join(yicesargs) + ')'
        return result

@yicesObj.register(Or)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(or ' + ' '.join(yicesargs) + ')'
        return result

@yicesObj.register(Implies)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(=> ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Beq)
def _(const):
    x = yicesObj(const.left())
    y = yicesObj(const.right())
    result = '(= ' + x + ' ' + y + ')'
    return result

@yicesObj.register(Not)
def _(const):
    x = yicesObj(const.child())
    result = '(not ' + x + ')'
    return result

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


    yicesresult = [yicesObj(c) for c in result]
    result = '(and ' + ' '.join(yicesresult) + ')'
    return result

@yicesObj.register(Forall)
def _(const):
    typeList = [i.getType() for i in const.condition.getVars()]
    if not(Type.Real in typeList):
        subCondition = yicesObj(const.condition.substitution(const.modeDict))
        return subCondition
    else:
        endCond = yicesObj(const.condition.substitution(const.endDict))
        startCond = yicesObj(const.condition.substitution(const.startDict))
        result = '(and ' + endCond + ' ' + startCond + ')'
        return result

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

    yicesresult = [yicesObj(c) for c in result]
    result = '(and ' + ' '.join(yicesresult) + ')'
    return result

