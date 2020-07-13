from stlmcPy.constraints.node import *
from stlmcPy.constraints.operations import substitution
from stlmcPy.core.differentiation import diff
from functools import singledispatch
import z3


def getConstraints(self: Integral):
    result = []
    subDict = {}
    for i in range(len(self.endList)):
        keyIndex = str(self.endList[i]).find('_')
        keyValue = str(self.endList[i])[0:keyIndex]
        subDict[keyValue] = self.startList[i]
    if self.flowType == 'diff':
        for i in self.ode.values():
            subvariables = list(i.getVars())
            '''
            for j in range(len(subvariables)):
                if subvariables[j] in self.ode.keys():
                    if str(self.ode[subvariables[j]]) == str(RealVal(0)):
                        pass
                    else:
                        print(str(self.ode[subvariables[j]]))
                        raise constODEerror()
            '''
        substitutionExp = {}
        for i in self.ode.keys():
            substitutionExp[str(i.id)] = substitution(self.ode[i], subDict)
        for i in range(len(self.endList)):
            keyIndex = str(self.endList[i]).find('_')
            keyValue = str(self.endList[i])[0:keyIndex]
            if keyValue in substitutionExp.keys():
                result.append(self.endList[i] == self.startList[i] + substitutionExp[keyValue] * self.time)
    elif self.flowType == 'sol':
        subDict['time'] = Real('tau_' + str(self.time.id)[4:])
        substitutionExp = {}
        for i in self.ode.keys():
            substitutionExp[str(i.id)] = substitution(self.ode[i], subDict)
        for i in range(len(self.endList)):
            keyIndex = str(self.endList[i]).find('_')
            keyValue = str(self.endList[i])[0:keyIndex]
            if keyValue in substitutionExp.keys():
                result.append(self.endList[i] == substitutionExp[keyValue])
    else:
        raise FlowTypeEerror()

    result.append(self.curMode)

    return result


def getForallConsts(const):
    exp = const.exp

    if len(exp.getVars()) == 0:
        return exp

    # If proposition is just boolean variable, return original expression
    if not (isinstance(exp, Gt) or isinstance(exp, Numeq) or isinstance(exp, Numneq) or isinstance(exp, Ge)):
        if exp.getType() == Type.Bool:
            return exp.substitution(const.modePropDict)
        else:
            print(exp)
            print(exp.getType())
            raise Exception("Proposition constraints something wrong")

    result = list()
    handlingExp = exp.left() - exp.right()
    handlingExp = substitution(handlingExp, const.modePropDict)
    substitutionExp = substitution(handlingExp, const.ode)
    diffExp = diff(substitutionExp)

    # monotone increase or decrease
    result.append(Or(Ge(diffExp, RealVal(0)), Le(diffExp, RealVal(0))))

    # Special case : a == b
    if isinstance(exp, Numeq):
        result.append(Numeq(handlingExp.substitution(const.startDict), RealVal(0)))
        result.append(Numeq(handlingExp.substitution(const.endDict), RealVal(0)))
        result.append(Numeq(diffExp, RealVal(0)))
    # Special case : a =/= b
    elif isinstance(exp, Numneq):
        subresult = list()
        subresult.append(
            Forall(const.curMode, const.propID, Gt(handlingExp, RealVal(0)), const.modePropDict, const.startDict,
                   const.endDict, const.ode, const.delta))
        subresult.append(
            Forall(const.curMode, const.propID, Lt(handlingExp, RealVal(0)), const.modePropDict, const.startDict,
                   const.endDict, const.ode, const.delta))
        result.append(Or(*subresult))
    else:
        # f(t') >= 0
        result.append(Ge(substitution(handlingExp, const.endDict), RealVal(0)))
        if isinstance(exp, Gt):
            # Check a start point of interval satisfies the proposition
            result.append(Gt(substitution(handlingExp, const.startDict), RealVal(0)))
            # Case : f(t) = 0 -> dot(f(T)) > 0, forall T in (t, t')
            result.append(Implies(substitution(handlingExp, const.startDict) == RealVal(0),
                                  Forall(const.curMode, const.propID, Gt(diffExp, RealVal(0)), const.modePropDict,
                                         const.startDict, const.endDict, const.ode, const.delta)))
            # Case : f(t') = 0 -> dot(f(T)) < 0, forall T in (t, t')
            result.append(Implies(substitution(handlingExp, const.endDict) == RealVal(0),
                                  Forall(const.curMode, const.propID, Lt(diffExp, RealVal(0)), const.modePropDict,
                                         const.startDict, const.endDict, const.ode, const.delta)))
        elif isinstance(exp, Ge):
            result.append(Ge(substitution(handlingExp, const.startDict), RealVal(0)))
            result.append(Implies(substitution(handlingExp, const.startDict) == RealVal(0),
                                  Forall(const.curMode, const.propID, Ge(diffExp, RealVal(0)), const.modePropDict,
                                         const.startDict, const.endDict, const.ode, const.delta)))
            result.append(Implies(substitution(handlingExp, const.endDict) == RealVal(0),
                                  Forall(const.curMode, const.propID, Le(diffExp, RealVal(0)), const.modePropDict,
                                         const.startDict, const.endDict, const.ode, const.delta)))

    return And(*result)


def z3checkSat(consts, logic):
    z3Consts=[z3Obj(c, False) for c in consts]

    if logic != "NONE":
        solver = z3.SolverFor(logic)
    else:
        solver = z3.Solver()

    #solver.set("timeout", timeout * 1000)
   # target_z3_simplify = z3.simplify(z3.And(*z3Consts))
    #solver.add(target_z3_simplify)
    solver.add(z3Consts)

    with open("thermoLinear.smt2", 'w') as fle:
        print(solver.to_smt2(), file=fle)


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
def z3Obj(const:Node, hylaa = False):
    raise NotImplementedError('Something wrong')

@z3Obj.register(Constant)
def _(const, hylaa = False):
    op = {Type.Bool: z3.BoolVal, Type.Real: z3.RealVal, Type.Int: z3.IntVal}
    if const.getType() == Type.Bool:
        value = True if const.value else False
    else:
        value = str(const.value)
    return op[const.getType()](value)

@z3Obj.register(Variable)
def _(const, hylaa = False):
    op = {Type.Bool: z3.Bool, Type.Real: z3.Real, Type.Int: z3.Int}
    return  op[const.getType()](str(const.id))

@z3Obj.register(Ge)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x >= y

@z3Obj.register(Gt)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x > y

@z3Obj.register(Le)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x <= y

@z3Obj.register(Lt)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x < y

@z3Obj.register(Numeq)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x == y

@z3Obj.register(Plus)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x + y

@z3Obj.register(Minus)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x - y

@z3Obj.register(Pow)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x**y

@z3Obj.register(Mul)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x * y

@z3Obj.register(Div)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x / y

@z3Obj.register(Neg)
def _(const, hylaa = False):
    x = z3Obj(const.child(), hylaa)
    return -x

@z3Obj.register(And)
def _(const, hylaa = False):
    z3args = [z3Obj(c, hylaa) for c in const.children]
    if len(z3args) < 1:
        return True
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.And(z3args)

@z3Obj.register(Or)
def _(const, hylaa = False):
    z3args = [z3Obj(c, hylaa) for c in const.children]
    if len(z3args) < 1:
        return True
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.Or(z3args)

@z3Obj.register(Implies)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return z3.Implies(x, y)

@z3Obj.register(Beq)
def _(const, hylaa = False):
    x = z3Obj(const.left(), hylaa)
    y = z3Obj(const.right(), hylaa)
    return x == y

@z3Obj.register(Not)
def _(const, hylaa = False):
    x = z3Obj(const.child(), hylaa)
    return z3.Not(x)

@z3Obj.register(Integral)
def _(const, hylaa = False):
    result = getConstraints(const)
    z3result = [z3Obj(c, hylaa) for c in result]
    return z3.And(z3result) 

@z3Obj.register(Forall)
def _(const, hylaa = False):
    if hylaa:
        return z3.BoolVal(True) 
    result = list()
    result.append(And(const.getCurMode(), const.propID))
    result.append(const.propID == getForallConsts(const))
    z3result = [z3Obj(c, hylaa) for c in result]
    return z3.And(z3result)

@z3Obj.register(Solution)
def _(const, hylaa = False):
    result = const.getConstraints()
    z3result = [z3Obj(c, hylaa) for c in result]
    return z3.And(z3result)

