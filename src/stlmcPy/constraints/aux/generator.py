from typing import List

from ..constraints import *


def variable(name: str, ty: str):
    type_dict = {'bool': Bool, 'real': Real, 'int': Int}
    if ty not in type_dict:
        return None
    return type_dict[ty](name)


def value(val: str, ty: str):
    type_dict = {'bool': BoolVal, 'real': RealVal, 'int': IntVal}
    if ty not in type_dict:
        return None
    return type_dict[ty](val)


def unary_expr(expr: Expr, ty: str):
    type_dict = {"sin": Sin, "cos": Cos, "tan": Tan, "sqrt": Sqrt,
                 "arcsin": Arcsin, "arccos": Arccos, "arctan": Arctan, "-": Neg}
    if ty not in type_dict:
        return None
    return type_dict[ty](expr)


def binary_expr(left: Expr, right: Expr, ty: str):
    type_dict = {'+': Add, '-': Sub, '*': Mul, '/': Div, '^': Pow}
    if ty not in type_dict:
        return None
    return type_dict[ty](left, right)


def binary_proposition(left: Expr, right: Expr, ty: str):
    type_dict = {'<=': Leq, '>=': Geq, "<": Lt, ">": Gt, "=": Eq, "!=": Neq}
    if ty not in type_dict:
        return None
    return type_dict[ty](left, right)


def unary_formula(child: Formula, ty: str):
    type_dict = {"not": Not}
    if ty not in type_dict:
        return None
    return type_dict[ty](child)


def binary_formula(left: Formula, right: Formula, ty: str):
    type_dict = {"=": EqFormula, "!=": NeqFormula, "->": Implies}
    if ty not in type_dict:
        return None
    return type_dict[ty](left, right)


def multinary_formula(children: List, ty: str):
    type_dict = {'and': And, 'or': Or}
    if ty not in type_dict:
        return None
    return type_dict[ty](children)


def unary_temporal_formula(local_t: Interval, global_t: Interval, child: Formula, ty: str):
    type_dict = {"[]": GloballyFormula, "<>": FinallyFormula}
    if ty not in type_dict:
        return None
    return type_dict[ty](local_t, global_t, child)


def binary_temporal_formula(local_t: Interval, global_t: Interval, left: Formula, right: Formula, ty: str):
    type_dict = {"U": UntilFormula, "R": ReleaseFormula}
    if ty not in type_dict:
        return None
    return type_dict[ty](local_t, global_t, left, right)


def dynamics(vs: List, es: List, ty: str):
    type_dict = {'ode': Ode, 'func': Function}
    if ty not in type_dict:
        return None
    return type_dict[ty](vs, es)
