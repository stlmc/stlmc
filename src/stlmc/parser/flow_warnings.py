"""Bounded, solver-free identity checks for polynomial solution flows.

Nonzero constant initial offsets are errors: no initial state can satisfy them.
Other warnings are advisory: identities may hold on restricted initial states.
Unsupported or oversized expressions are skipped, not certified as valid.
"""
from fractions import Fraction
import warnings

from ..constraints.constraints import (
    Add, Constant, Div, Mul, Neg, Pow, Sub, Variable,
)
from ..exceptions import NotSupportedError


class ClosedFormFlowWarning(UserWarning):
    """Initial-value or subdivision consistency of a solution flow is suspect."""


class InvalidSolutionFlowError(NotSupportedError):
    """A closed-form flow provably contradicts its initial value."""


def _add(left, right, sign=1):
    result = dict(left)
    for term, coefficient in right.items():
        result[term] = result.get(term, Fraction(0)) + sign*coefficient
        if not result[term]:
            del result[term]
    if len(result) > 256:
        raise ValueError('polynomial size limit')
    return result


def _mul(left, right):
    if len(left)*len(right) > 4096:
        raise ValueError('polynomial size limit')
    result = {}
    for a, x in left.items():
        for b, y in right.items():
            if len(a)+len(b) > 64:
                raise ValueError('polynomial degree limit')
            term = tuple(sorted(a+b))
            result[term] = result.get(term, Fraction(0)) + x*y
    result = {term: value for term, value in result.items() if value}
    if len(result) > 256:
        raise ValueError('polynomial size limit')
    return result


def _polynomial(expression):
    if isinstance(expression, Constant):
        number = Fraction(expression.value)
        return {(): number} if number else {}
    if isinstance(expression, Variable):
        return {(expression.id,): Fraction(1)}
    if isinstance(expression, Neg):
        return _add({}, _polynomial(expression.child), -1)
    if isinstance(expression, (Add, Sub)):
        return _add(_polynomial(expression.left), _polynomial(expression.right),
                    -1 if isinstance(expression, Sub) else 1)
    if isinstance(expression, Mul):
        return _mul(_polynomial(expression.left), _polynomial(expression.right))
    if isinstance(expression, Div):
        denominator = _polynomial(expression.right)
        if set(denominator) != {()}:
            raise ValueError('nonconstant or zero denominator')
        return {term: value/denominator[()]
                for term, value in _polynomial(expression.left).items()}
    if isinstance(expression, Pow):
        exponent = _polynomial(expression.right)
        if set(exponent).difference({()}):
            raise ValueError('nonconstant exponent')
        number = exponent.get((), Fraction(0))
        if number.denominator != 1 or not 0 <= number <= 8:
            raise ValueError('unsupported exponent')
        result, base = {(): Fraction(1)}, _polynomial(expression.left)
        for _ in range(int(number)):
            result = _mul(result, base)
        return result
    raise ValueError('unsupported expression')


def _substitute(polynomial, mapping):
    result = {}
    for term, coefficient in polynomial.items():
        product = {(): coefficient}
        for name in term:
            product = _mul(product, mapping.get(name, {(name,): Fraction(1)}))
        result = _add(result, product)
    return result


def validate_solution_flow(variables, expressions, file_name, locations):
    """Check F(0,x)=x and vector restart identity without solving a model."""
    try:
        polynomials = {}
        for variable, expression in zip(variables, expressions):
            try:
                polynomials[variable.id] = _polynomial(expression)
            except (ValueError, ZeroDivisionError, OverflowError, RecursionError):
                continue
        failures = []
        definite = []
        for name, polynomial in polynomials.items():
            difference = _add(_substitute(polynomial, {'time': {}}),
                              {(name,): Fraction(1)}, -1)
            if difference:
                offset = str(difference[()]) if set(difference) == {()} else 'state-dependent'
                failures.append((name, offset))
                if set(difference) == {()}:
                    definite.append((name, offset))
        if failures:
            token = locations[(definite or failures)[0][0]]
            message = ('FLOW_INITIAL_VALUE: solution flow at t=0 is not '
                'identically its initial value: {}. Check admissible initial '
                'states and flow equations; verification may be misleading. '
                'The model has not been modified.').format(
                    ', '.join('{} (offset {})'.format(*item) for item in failures))
            if definite:
                message = ('{}:{}:{}: FLOW_INITIAL_VALUE: invalid solution '
                    'flow: nonzero constant initial offset for {}. F(0,x)=x '
                    'cannot hold for any initial state. Correct the flow '
                    'equations; verification was not started.').format(
                        file_name, token.line, token.column,
                        ', '.join('{} (offset {})'.format(*item) for item in definite))
        else:
            if len(polynomials) != len(variables):
                return
            symbols = {n for p in polynomials.values() for term in p for n in term}
            first, second = '__flow_check_s', '__flow_check_t'
            while first in symbols or second in symbols:
                first += '_'
                second += '_'
            s, t = {(first,): Fraction(1)}, {(second,): Fraction(1)}
            # Simultaneous state substitutions, including coupled flows.
            mapping = {name: _substitute(p, {'time': t})
                       for name, p in polynomials.items()}
            mapping['time'] = s
            failures = [name for name, p in polynomials.items()
                        if _add(_substitute(p, mapping),
                                _substitute(p, {'time': _add(s, t)}), -1)]
            if not failures:
                return
            token = locations[failures[0]]
            message = ('FLOW_SUBDIVISION: solution flow does not satisfy '
                'F(s+t,x)=F(s,F(t,x)) for arbitrary initial states: {}. '
                'Additional STL partition points may change the trajectory. '
                'Check initial-state restrictions or represent the required '
                'clock/state explicitly. The model has not been modified.').format(
                    ', '.join(failures))
    except (ValueError, ZeroDivisionError, OverflowError, RecursionError):
        return
    if definite:
        raise InvalidSolutionFlowError(message)
    # Keep warning emission outside the unsupported-expression handler; warning
    # filters configured as errors must propagate normally.
    warnings.warn_explicit(message, ClosedFormFlowWarning, file_name, token.line)
