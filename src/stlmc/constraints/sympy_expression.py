"""Structural arithmetic conversion; never parse/evaluate model text."""
from functools import reduce

import sympy

from ..exceptions import NotSupportedError
from .constraints import Add, Constant, Div, Mul, Neg, Pow, RealVal, Sub, Variable


class SympyExpression:
    """One conversion context preserves typed variable identity both ways."""
    def __init__(self):
        self.symbols = {}
        self.variables = {}

    def symbol(self, variable):
        key = (variable.type, variable.id)
        if key not in self.symbols:
            symbol = sympy.Dummy(variable.id, real=True)
            self.symbols[key] = symbol
            self.variables[symbol] = variable
        return self.symbols[key]

    def to_sympy(self, expression):
        if isinstance(expression, Constant):
            try:
                return sympy.Rational(str(expression.value))
            except (ValueError, TypeError) as error:
                raise NotSupportedError('non-rational arithmetic constant') from error
        if isinstance(expression, Variable):
            return self.symbol(expression)
        if isinstance(expression, Neg):
            return -self.to_sympy(expression.child)
        if isinstance(expression, (Add, Sub, Mul, Div, Pow)):
            left, right = self.to_sympy(expression.left), self.to_sympy(expression.right)
            if isinstance(expression, Div) and right == 0:
                raise NotSupportedError('zero denominator in symbolic arithmetic')
            if isinstance(expression, Add):
                return left + right
            if isinstance(expression, Sub):
                return left - right
            if isinstance(expression, Mul):
                return left * right
            if isinstance(expression, Div):
                return left / right
            return left ** right
        raise NotSupportedError('unsupported expression for symbolic differentiation: {}'.format(
            type(expression).__name__))

    def from_sympy(self, expression):
        if expression in self.variables:
            return self.variables[expression]
        if isinstance(expression, sympy.Rational):
            numerator = RealVal(str(abs(expression.p)))
            value = numerator if expression.q == 1 else Div(numerator, RealVal(str(expression.q)))
            return Neg(value) if expression.p < 0 else value
        if isinstance(expression, (sympy.Add, sympy.Mul)):
            operation = Add if isinstance(expression, sympy.Add) else Mul
            return reduce(operation, (self.from_sympy(child) for child in expression.args))
        if isinstance(expression, sympy.Pow):
            base, exponent = expression.args
            if exponent.is_Integer and exponent < 0:
                denominator = self.from_sympy(base) if exponent == -1 else Pow(
                    self.from_sympy(base), RealVal(str(-exponent)))
                return Div(RealVal('1'), denominator)
            return Pow(self.from_sympy(base), self.from_sympy(exponent))
        raise NotSupportedError('unsupported SymPy arithmetic result: {}'.format(expression))
