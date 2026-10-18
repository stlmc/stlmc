"""Text formatting helpers for constraint expressions."""

from functools import singledispatch

from .constraints import (
    Add, And, Constraint, Div, Eq, Forall, Geq, Gt, Leq, Lt, Mul, Neg, Neq,
    Pow, Sub, Variable, Or, Not, Implies, UnaryTemporalFormula,
    BinaryTemporalFormula, Unary, Binary, Reach, Interval,
)
from .boolean_simplification import flatten_boolean


def format_constraint(const):
    """Render a constraint with display-only Boolean flattening at every level."""
    if isinstance(const, (And, Or)):
        reduced = flatten_boolean(const)
        if not isinstance(reduced, (And, Or)):
            return format_constraint(reduced)
        operator = 'and' if isinstance(reduced, And) else 'or'
        return '(' + operator + ' ' + ' '.join(map(format_constraint, reduced.children)) + ')'
    if isinstance(const, UnaryTemporalFormula):
        return '({}{} {})'.format(const._op_str, format_constraint(const.local_time), format_constraint(const.child))
    if isinstance(const, BinaryTemporalFormula):
        return '({} {}{} {})'.format(format_constraint(const.left), const._op_str,
                                    format_constraint(const.local_time), format_constraint(const.right))
    if isinstance(const, Interval):
        return '{}{},{}{}'.format('[' if const.left_end else '(', format_constraint(const.left),
                                 format_constraint(const.right), ']' if const.right_end else ')')
    if isinstance(const, Forall):
        return '(forall {} . {})'.format(const.current_mode_number, format_constraint(const.const))
    if isinstance(const, Reach):
        return 'reach ' + format_constraint(const.formula)
    if isinstance(const, Unary):
        return '({} {})'.format(const._op_str, format_constraint(const.child))
    if isinstance(const, Binary):
        return '({} {} {})'.format(format_constraint(const.left), const._op_str, format_constraint(const.right))
    return str(const)


@singledispatch
def infix(const: Constraint):
    return format_constraint(const)


@infix.register(Variable)
def _(const: Variable):
    return const.id


@infix.register(And)
@infix.register(Or)
def _(const):
    reduced = flatten_boolean(const)
    if not isinstance(reduced, (And, Or)):
        return infix(reduced)
    separator = ' & ' if isinstance(reduced, And) else ' | '
    return '(' + separator.join(infix(child) for child in reduced.children) + ')'


@infix.register(Not)
def _(const):
    return '(not {})'.format(infix(const.child))


@infix.register(Implies)
def _(const):
    return '({} -> {})'.format(infix(const.left), infix(const.right))


@infix.register(Geq)
def _(const: Geq):
    return infix(const.left) + " >= " + infix(const.right)


@infix.register(Gt)
def _(const: Gt):
    return infix(const.left) + " > " + infix(const.right)


@infix.register(Leq)
def _(const: Leq):
    return infix(const.left) + " <= " + infix(const.right)


@infix.register(Lt)
def _(const: Lt):
    return infix(const.left) + " < " + infix(const.right)


@infix.register(Eq)
def _(const: Eq):
    return infix(const.left) + " == " + infix(const.right)


@infix.register(Neq)
def _(const: Neq):
    return infix(const.left) + " != " + infix(const.right)


@infix.register(Add)
def _(const: Add):
    return "(" + infix(const.left) + " + " + infix(const.right) + ")"


@infix.register(Sub)
def _(const: Sub):
    return "(" + infix(const.left) + " - " + infix(const.right) + ")"


@infix.register(Neg)
def _(const: Neg):
    return "(-" + infix(const.child) + ")"


@infix.register(Mul)
def _(const: Mul):
    return "(" + infix(const.left) + " * " + infix(const.right) + ")"


@infix.register(Div)
def _(const: Div):
    return "(" + infix(const.left) + " / " + infix(const.right) + ")"


@infix.register(Pow)
def _(const: Pow):
    return "(" + infix(const.left) + " ** " + infix(const.right) + ")"


@infix.register(Forall)
def _(const: Forall):
    return infix(const.const)
