from functools import singledispatch

from stlmcPy.constraints.constraints import UnaryFunc, BinaryExp, CompCond, Multy, Binary, Unary, UnaryJump, DiffEq, \
    SolEq, flowDecl, jumpRedeclModule, jumpMod, propDecl
from stlmcPy.constraints.node import *


@singledispatch
def get_expression(exp: Variable, var_dict):
    return {'bool': Bool, 'int': Int, 'real': Real}[exp.type](exp.id)


@get_expression.register(UnaryFunc)
def _(exp: UnaryFunc, var_dict):
    if str(exp.val) in var_dict.keys():
        degree = var_dict[str(exp.val)]
    elif str(exp.val).isdigit():
        degree = RealVal(float(exp.val))
    else:
        degree = Real(str(exp.val))
    if exp.func == 'sin':
        return degree - degree * degree * degree / RealVal(6)
    elif exp.func == 'cos':
        return degree - degree * degree / RealVal(2)
    elif exp.func == 'tan':
        return degree + degree * degree * degree
    elif exp.func == '-':
        return RealVal(0) - degree
    else:
        raise Exception("Not yet in Unary function")


@get_expression.register(BinaryExp)
def _(exp: BinaryExp, var_dict):
    left = exp.left
    right = exp.right
    if isinstance(left, BinaryExp) or isinstance(left, UnaryFunc):
        left = get_expression(left, var_dict)
    if isinstance(right, BinaryExp) or isinstance(right, UnaryFunc):
        right = get_expression(right, var_dict)
    if str(exp.left) in var_dict.keys():
        left = var_dict[str(var_dict.left)]
    if str(exp.right) in var_dict.keys():
        right = var_dict[str(var_dict.right)]
    else:
        pass

    if exp.op == '+':
        return (left + right)
    elif exp.op == '-':
        return (left - right)
    elif exp.op == '*':
        return (left * right)
    elif exp.op == '/':
        return (left / right)
    elif exp.op == '**':
        return (left ** right)
    else:
        raise Exception("Not yet in Binary Expression")


@get_expression.register(CompCond)
def _(exp: CompCond, var_dict):
    left = exp.left
    right = exp.right
    if isinstance(left, BinaryExp):
        left = get_expression(left, var_dict)
    if isinstance(right, BinaryExp):
        right = get_expression(right, var_dict)
    if str(exp.left) in var_dict.keys():
        left = var_dict[str(exp.left)]
    if str(exp.right) in var_dict.keys():
        right = var_dict[str(exp.right)]
    if exp.op == '<':
        return left < right
    elif exp.op == '<=':
        return left <= right
    elif exp.op == '>':
        return left > right
    elif exp.op == '>=':
        return left >= right
    elif exp.op == '=':
        return left == right
    elif exp.op == '!=':
        return left != right
    else:
        raise Exception("Not yet in Compare Condition")


@get_expression.register(Multy)
def _(exp: Multy, var_dict):
    result = list()
    for i in range(len(exp.props)):
        if isinstance(exp.props[i], NextVar):
            expr = exp.props[i]
        elif exp.props[i] in var_dict.keys():
            expr = var_dict[exp.props[i]]
        else:
            expr = get_expression(exp.props[i], var_dict)
        result.append(expr)
    return {'and': And, 'or': Or}[exp.op](*result)


@get_expression.register(Binary)
def _(exp: Binary, var_dict):
    if str(exp.left) in var_dict.keys():
        left = var_dict[str(exp.left)]
    else:
        left = get_expression(exp.left, var_dict)

    if str(exp.right) in var_dict.keys():
        right = var_dict[str(exp.right)]
    else:
        right = get_expression(exp.right, var_dict)
    return {'and': And, 'or': Or}[exp.op](left, right)


@get_expression.register(Unary)
def _(exp: Unary, var_dict):
    if exp.prop in var_dict.keys():
        prop = var_dict[exp.prop]
    else:
        prop = get_expression(exp.prop, var_dict)
    return {'not': Not, '~': Not}[exp.op](prop)


@get_expression.register(UnaryJump)
def _(exp: UnaryJump, var_dict):
    if isinstance(exp.prop, NextVar):
        prop = exp.prop
    else:
        prop = get_expression(exp.prop, var_dict)
    return {'not': Not, 'Not': Not, '~': Not}[exp.op](prop)


@get_expression.register(DiffEq)
def _(exp: DiffEq, var_dict):
    result = dict()
    result[exp.contVar] = get_expression(exp.flow, var_dict)
    return result


@get_expression.register(SolEq)
def _(exp: SolEq, var_dict):
    result = dict()
    result[exp.contVar] = get_expression(exp.flow, var_dict)
    return result


@get_expression.register(flowDecl)
def _(exp: flowDecl, var_dict):
    return exp.exps


@get_expression.register(jumpRedeclModule)
def _(exp: jumpRedeclModule, var_dict):
    condition = get_expression(exp.cond, var_dict)
    redecl = get_expression(exp.jumpRedecl, var_dict)
    return And(condition, redecl)


@get_expression.register(jumpMod)
def _(exp: jumpMod, var_dict):
    if exp.nextVarId in var_dict.keys():
        left = NextVar(var_dict[exp.nextVarId])
    if isinstance(exp.exp, Constant):
        right = exp.exp
    elif type(exp.exp) in [Real, Int, Bool]:
        right = exp.exp
    elif exp.exp in var_dict.keys():
        right = var_dict[exp.exp]
    else:
        right = exp.exp.getExpression(var_dict)

    if exp.op == '<':
        return left < right
    elif exp.op == '<=':
        return left <= right
    elif exp.op == '>':
        return left > right
    elif exp.op == '>=':
        return left >= right
    elif exp.op == '=':
        return left == right
    elif exp.op == '!=':
        return left != right
    else:
        raise Exception("jump undeclared variable id in next variable handling")


@get_expression.register(propDecl)
def _(exp: propDecl, var_dict):
    if exp.cond in var_dict.keys():
        return var_dict[exp.cond]
    return get_expression(exp.cond, var_dict)


# ======= node.py =======
@get_expression.register(Constant)
def _(exp: Constant, sub_dict):
    op = {Type.Bool: Bool, Type.Int: Int, Type.Real: Real}
    return op[exp.type](str(exp.cvalue))


