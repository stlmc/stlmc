"""Parse numeric data, never Python or symbolic expression strings."""

from fractions import Fraction
import math
import re

MAX_NUMBER_LENGTH = 4096
MAX_DECIMAL_EXPONENT = 10000
MAX_NUMBER_WRAPPERS = 16

_SCALAR = r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?"
_SCALAR_RE = re.compile(_SCALAR)
_RATIO_RE = re.compile(r"(" + _SCALAR + r")\s*/\s*(" + _SCALAR + r")")
_SMT_RATIO_RE = re.compile(r"\(/\s+(" + _SCALAR + r")\s+(" + _SCALAR + r")\s*\)")


def _scalar(text):
    exponent = re.search(r"[eE]([+-]?[0-9]+)$", text)
    if exponent and abs(int(exponent.group(1))) > MAX_DECIMAL_EXPONENT:
        raise ValueError("numeric exponent exceeds supported limit")
    return Fraction(text)


def parse_number(value):
    """Return an exact Fraction for finite data, or a float infinity.

    Accepted legacy solver forms include ``(1/2)``, ``(/ 1 2)`` and
    ``(- (/ 1 2))``. Operators other than a scalar quotient/unary sign,
    identifiers, function calls, NaN and executable syntax are rejected.
    """
    if isinstance(value, bool):
        raise ValueError("Boolean is not a numeric value")
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, float):
        if math.isnan(value):
            raise ValueError("NaN is not a numeric value")
        if math.isinf(value):
            return value
        return Fraction(str(value))
    if not isinstance(value, str) or len(value) > MAX_NUMBER_LENGTH:
        raise ValueError("invalid or oversized numeric value")
    text = value.strip()
    sign = 1
    for _ in range(MAX_NUMBER_WRAPPERS):
        lower = text.lower()
        if lower in ('inf', '+inf', 'infinity', '+infinity', 'oo', '+oo'):
            return sign * math.inf
        if lower in ('-inf', '-infinity', '-oo'):
            return -sign * math.inf
        if _SCALAR_RE.fullmatch(text):
            return sign * _scalar(text)
        match = _RATIO_RE.fullmatch(text) or _SMT_RATIO_RE.fullmatch(text)
        if match:
            try:
                return sign * _scalar(match.group(1)) / _scalar(match.group(2))
            except ZeroDivisionError as error:
                raise ValueError("zero denominator in numeric value") from error
        if text.startswith('(- ') and text.endswith(')'):
            sign *= -1
            text = text[3:-1].strip()
        elif text.startswith('(') and text.endswith(')'):
            text = text[1:-1].strip()
        else:
            break
    raise ValueError("invalid numeric value")


def number_float(value):
    """Convert validated numeric data to the sampling float domain."""
    number = parse_number(value)
    try:
        return float(number)
    except OverflowError:
        return -math.inf if number < 0 else math.inf
