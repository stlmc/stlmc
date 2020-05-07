from dreal import *
from dreal import And as drealAnd
from dreal import Or as drealOr
from dreal import Not as drealNot
from dreal import Implies as drealImplies
from .drealTerms import * 
from functools import singledispatch
from .node import *
from .error import *

# return a check result and the Z3 constraint size
def drealcheckSat(consts, logic):
    termDict = drealDeclared(consts)
    drealConsts = [drealObj(c, termDict) for c in consts]
    f_sat = drealAnd(*drealConsts)
    termList = list(termDict.values())
    b = Box(termList)

    result = CheckSatisfiability(f_sat, 0.001, b)
    print(result)

    if result:
        result = False
    else:
        b = None
        result = True if not (result)  else "Unknown"

    return (result, -1, b)

# return the size of the Z3 constraint
'''
def sizeAst(node:Terms):
    if node == Terms.NULL_TERM:
        return 0
    retval = yapi.yices_term_num_children(node)
    if retval == -1:
        return 0
    else:
        return 1 + sum([sizeAst(yapi.yices_term_child(node, c)) for c in range(retval)])
'''

@singledispatch
def drealObj(const:Node, termDict):
    print(type(const))
    print(const)
    raise NotImplementedError('Something wrong')

@drealObj.register(Constant)
def _(const, termDict):
    if const.getType() == Type.Bool:
        value = Formula.TRUE() if const.value else Formula.FALSE()
        return value
    return float(str(const.value))

@drealObj.register(Variable)
def _(const, termDict):
    if not (str(const.id) in termDict.keys()):
        raise error.drealDeclTermError()
    return termDict[str(const.id)] 

@drealObj.register(Ge)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x >= y)

@drealObj.register(Gt)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x > y) 

@drealObj.register(Le)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x <= y)

@drealObj.register(Lt)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x < y) 

@drealObj.register(Numeq)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x == y) 

@drealObj.register(Plus)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x + y)

@drealObj.register(Minus)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x - y)

@drealObj.register(Pow)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)

    return (x ** y)

@drealObj.register(Mul)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x * y)

@drealObj.register(Div)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    return (x / y)

@drealObj.register(Neg)
def _(const, termDict):
    x = drealObj(const.child(), termDict)
    return -x

@drealObj.register(And)
def _(const, termDict):
    drealargs = list()
    for c in const.children:
        sub = drealObj(c, termDict)
        if isinstance(sub, bool):
            sub = Formula.TRUE() if sub else Formula.FALSE()
        drealargs.append(sub)
    if len(drealargs) < 1:
        return Formula.TRUE()
    elif len(drealargs) < 2:
        return drealargs[0]
    else:
        return drealAnd(*drealargs)

@drealObj.register(Or)
def _(const, termDict):
    drealargs = list()
    for c in const.children:
        sub = drealObj(c, termDict)
        if isinstance(sub, bool):
            sub = Formula.TRUE() if sub else Formula.FALSE()
        drealargs.append(sub)
    #drealargs = [drealObj(c, termDict) for c in const.children]
    if len(drealargs) < 1:
        return Formula.TRUE()
    elif len(drealargs) < 2:
        return drealargs[0]
    else:
        result = drealOr(*drealargs)
        return result

@drealObj.register(Implies)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    if isinstance(x, bool):
        x = Formula.TRUE() if x else Formula.FALSE()
    if isinstance(y, bool):
        y = Formula.TRUE() if y else Formula.FALSE()
    return drealImplies(x, y)

@drealObj.register(Beq)
def _(const, termDict):
    x = drealObj(const.left(), termDict)
    y = drealObj(const.right(), termDict)
    if isinstance(x, bool):
        x = Formula.TRUE() if x else Formula.FALSE()
    if isinstance(y, bool):
        y = Formula.TRUE() if y else Formula.FALSE()
    return (x == y)

@drealObj.register(Not)
def _(const, termDict):
    x = drealObj(const.child(), termDict)
    if isinstance(x, bool):
        x = Formula.TRUE() if x else Formula.FALSE()
    return drealNot(x)

@drealObj.register(Integral)
def _(const, termDict):
    result = const.getConstraints()
    drealresult = [drealObj(c, termDict) for c in result]
    return drealAnd(*drealresult)

@drealObj.register(Forall)
def _(const, termDict):
    exp = const.exp
    # Change proposition formula type to Gt or Ge
    if isinstance(exp, Lt):
        exp = Gt((exp.right() - exp.left()), RealVal(0))
    if isinstance(exp, Le):
        exp = Ge((exp.right() - exp.left()), RealVal(0))

    # If proposition is just boolean variable, return original expression
    if not (isinstance(exp, Gt) or isinstance(exp, Numeq) or isinstance(exp, Numneq) or isinstance(exp, Ge)):
        if exp.getType() == Type.Bool:
            return drealObj(exp.substitution(const.modePropDict), termDict)
        else:
            print(exp)
            print(exp.getType())
            raise ("Proposition constraints something wrong")

    # Case Real value >(or >=) 0
    if len(exp.getVars()) == 0:
        return drealObj(exp, termDict)

    handlingExp = exp.left() - exp.right()
    handlingExp = handlingExp.substitution(const.modePropDict)
    substitutionExp = handlingExp.substitution(const.ode)
    curTime = list(substitutionExp.getVars())
    if not(len(curTime) == 1):
        raise ("dReal Forall time error")
    curBound = str(curTime[0].id)[4:]
    return forall(list(termDict.values()), drealImplies(drealAnd(termDict[str(curTime[0].id)] < termDict['tau_' + str(int(curBound)+1)], 
                                                        termDict[str(curTime[0].id)] >= termDict['tau_'+str(curBound)]),
                                                        drealObj(exp, termDict)))

@drealObj.register(Solution)
def _(const, termDict):
    result = const.getConstraints()
    drealresult = [drealObj(c, termDict) for c in result]
    return drealAnd(*drealresult)
