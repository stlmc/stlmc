import z3
import itertools
from functools import singledispatch
from .node import *
from .makeForallConsts import *

# return a check result and the Z3 constraint size
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
    for c in range(len(z3Consts)):
        print(c)
        print(z3Consts[c])

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
    print(type(const))
    print(const)
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
    result = const.getConstraints()
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

