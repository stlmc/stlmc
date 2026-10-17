"""SymPy-backed differentiation with explicit flow-time interpretation."""
from fractions import Fraction

import sympy

from ..exceptions import NotSupportedError
from .analysis import get_vars
from .constraints import (
    Add, Constant, Constraint, Div, Expr, Function, Integral, Mul, Neg, Ode,
    Pow, Real, RealVal, Sub, Variable,
)
from .substitution import substitution
from .sympy_expression import SympyExpression


def diff(exp: Expr, integral: Integral):
    new_exp = substitution(exp, make_diff_mapping(integral))
    if isinstance(integral.dynamics, Function):
        end_id = integral.end_vector[0].id
        bound = end_id[end_id.find('_') + 1:end_id.rfind('_')]
        # Hold the start clock and initial state fixed; do NOT set them to zero.
        return differentiate_polynomial(new_exp, Real('tau_' + str(int(bound) + 1)))
    if not supports_symbolic_differentiation(new_exp):
        raise NotSupportedError('cannot apply polynomial invariant simplification to {}'.format(new_exp))
    return diff_aux(new_exp)


def _validate_polynomial(expression, variable):
    """Reject clock denominators/powers BEFORE SymPy can cancel them away."""
    if variable not in get_vars(expression):
        return
    if isinstance(expression, Variable):
        return
    if isinstance(expression, Neg):
        return _validate_polynomial(expression.child, variable)
    if isinstance(expression, (Add, Sub, Mul)):
        _validate_polynomial(expression.left, variable)
        _validate_polynomial(expression.right, variable)
        return
    if isinstance(expression, Div) and variable not in get_vars(expression.right):
        return _validate_polynomial(expression.left, variable)
    if isinstance(expression, Pow) and not get_vars(expression.right):
        exponent = _constant_value(expression.right)
        if exponent.denominator == 1 and exponent >= 0:
            return _validate_polynomial(expression.left, variable)
    raise NotSupportedError('cannot apply polynomial invariant simplification to {}'.format(expression))


def differentiate_polynomial(expression, variable):
    """Differentiate only the nominated clock; other symbols are parameters."""
    if variable not in get_vars(expression):
        return RealVal('0')
    _validate_polynomial(expression, variable)
    context = SympyExpression()
    converted = context.to_sympy(expression)
    result = sympy.diff(converted, context.symbol(variable))
    return context.from_sympy(result)


def supports_symbolic_differentiation(const: Constraint) -> bool:
    """Compatibility capability check for the legacy ODE simplification path."""
    if isinstance(const, (Constant, Variable)):
        return True
    if isinstance(const, Neg):
        return supports_symbolic_differentiation(const.child)
    if isinstance(const, (Add, Sub, Mul, Div)):
        return (supports_symbolic_differentiation(const.left)
                and supports_symbolic_differentiation(const.right))
    if isinstance(const, Pow):
        if not isinstance(const.left, Variable) or get_vars(const.right):
            return False
        try:
            _constant_value(const.right)
        except (NotSupportedError, ValueError, ZeroDivisionError):
            return False
        return True
    return False


def make_diff_mapping(integral: Integral):
    result = {}
    for index, dyn_var in enumerate(integral.start_vector):
        if not isinstance(integral.dynamics, Ode):
            result[dyn_var] = integral.dynamics.exps[index]
            continue
        end_id = integral.end_vector[0].id
        bound = end_id[end_id.find('_') + 1:end_id.rfind('_')]
        end_tau = Real('tau_' + str(int(bound) + 1))
        result[dyn_var] = Mul(integral.dynamics.exps[index], end_tau)
    return result


def diff_aux(const: Constraint):
    """Legacy directional derivative: advance all tau clocks together.

    Kept for the existing ODE path and compatibility imports. Closed-form
    flows MUST use differentiate_polynomial with one explicit local clock.
    No hand-written differentiation rules or fallback remain here.
    """
    context = SympyExpression()
    expression = context.to_sympy(const)
    clocks = [v for v in get_vars(const) if str(v.id).startswith('tau')]
    result = sum((sympy.diff(expression, context.symbol(v)) for v in clocks), sympy.Integer(0))
    return context.from_sympy(result)


def _constant_value(const):
    context = SympyExpression()
    value = context.to_sympy(const)
    if not isinstance(value, sympy.Rational):
        raise NotSupportedError('expected a rational constant arithmetic expression')
    return Fraction(int(value.p), int(value.q))
