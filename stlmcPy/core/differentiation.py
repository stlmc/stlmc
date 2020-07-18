# from functools import singledispatch
# from stlmcPy.constraints.node import *
# import z3
#
#
# @singledispatch
# def diff(const: Node):
#     raise NotImplementedError('Something wrong')
#
#
# @diff.register(Constant)
# def _(const):
#     return RealVal(0)
#
#
# @diff.register(Variable)
# def _(const):
#     if str(const.id)[0:4] == 'time':
#         return RealVal(1)
#     else:
#         return RealVal(0)
#
#
# @diff.register(Plus)
# def _(const):
#     x = const.left()
#     y = const.right()
#
#     if len(const.getVars()) == 0:
#         return RealVal(0)
#     if len(x.getVars()) == 0:
#         return diff(y)
#     if len(y.getVars()) == 0:
#         return diff(x)
#
#     return diff(x) + diff(y)
#
#
# @diff.register(Minus)
# def _(const):
#     x = const.left()
#     y = const.right()
#
#     if len(const.getVars()) == 0:
#         return RealVal(0)
#     if len(x.getVars()) == 0:
#         return diff(y)
#     if len(y.getVars()) == 0:
#         return diff(x)
#
#     return diff(x) - diff(y)
#
#
# @diff.register(Pow)
# def _(const):
#     x = const.left()
#     y = const.right()
#
#     if isinstance(x, Variable) and (len(y.getVars()) == 0):
#         if eval(str(y)) == 0:
#             return RealVal(0)
#         elif str(x.id[0:4] == 'time'):
#             return (y * (x ** (y - RealVal(1))))
#         else:
#             return RealVal(0)
#     else:
#         print(type(const))
#         print(const)
#         raise NotImplementedError('Cannot hanlindg polynomial yet')
#
#
# @diff.register(Mul)
# def _(const):
#     x = const.left()
#     y = const.right()
#
#     if len(const.getVars()) == 0:
#         return RealVal(0)
#     if len(x.getVars()) == 0:
#         return x * diff(y)
#     if len(y.getVars()) == 0:
#         return diff(x) * y
#
#     return diff(x) * y + x * diff(y)
#
#
# @diff.register(Div)
# def _(const):
#     x = const.left()
#     y = const.right()
#     if len(const.getVars()) == 0:
#         return RealVal(0)
#     if len(x.getVars()) == 0:
#         return RealVal(0) - diff(y) * x / (y * y)
#     if len(y.getVars()) == 0:
#         return diff(x) / y
#
#     return diff(x) / y - diff(y) * x / (y * y)
#
#
# @diff.register(Neg)
# def _(const):
#     x = diff(const.child())
#     return -x
