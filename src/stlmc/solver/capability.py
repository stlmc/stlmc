from decimal import Decimal, InvalidOperation

from ..constraints.constraints import (
    Arccos, Arcsin, Arctan, Binary, Constraint, Cos, Dynamics, IntVal,
    Multinary, Pow, RealVal, Sin, Sqrt, Tan, Unary,
)
from ..exceptions import NotSupportedError


TRANSCENDENTAL = (Sqrt, Sin, Cos, Tan, Arcsin, Arccos, Arctan)
TRANSCENDENTAL_NAMES = {
    Sqrt: "sqrt", Sin: "sin", Cos: "cos", Tan: "tan",
    Arcsin: "arcsin", Arccos: "arccos", Arctan: "arctan",
}


def _conversion_error(solver, operator, expression, detail=None):
    message = "solver '{}' does not support {} in expression {}".format(
        solver, operator, expression
    )
    if detail:
        message = "{} ({})".format(message, detail)
    raise NotSupportedError(message)


def _is_nonnegative_integer_constant(expression):
    if not isinstance(expression, (RealVal, IntVal)):
        return False
    try:
        value = Decimal(str(expression.value))
    except InvalidOperation:
        return False
    return value.is_finite() and value >= 0 and value == value.to_integral_value()


def _validate_expression(solver, expression):
    if solver in {"z3", "yices"} and isinstance(expression, TRANSCENDENTAL):
        _conversion_error(
            solver, TRANSCENDENTAL_NAMES[type(expression)], expression,
            "use dReal for transcendental arithmetic",
        )
    if solver in {"z3", "yices"} and isinstance(expression, Pow):
        if not _is_nonnegative_integer_constant(expression.right):
            _conversion_error(
                solver, "non-integer or symbolic exponentiation", expression,
                "only non-negative integer constant exponents are supported",
            )

    if isinstance(expression, Dynamics):
        for child in expression.exps:
            _validate_expression(solver, child)
    elif isinstance(expression, Unary):
        _validate_expression(solver, expression.child)
    elif isinstance(expression, Binary):
        _validate_expression(solver, expression.left)
        _validate_expression(solver, expression.right)
    elif isinstance(expression, Multinary):
        for child in expression.children:
            _validate_expression(solver, child)


def expression_requires_dreal(expression):
    if isinstance(expression, TRANSCENDENTAL):
        return True
    if isinstance(expression, Pow) and not _is_nonnegative_integer_constant(
        expression.right
    ):
        return True
    if isinstance(expression, Dynamics):
        return any(expression_requires_dreal(child) for child in expression.exps)
    if isinstance(expression, Unary):
        return expression_requires_dreal(expression.child)
    if isinstance(expression, Binary):
        return (
            expression_requires_dreal(expression.left)
            or expression_requires_dreal(expression.right)
        )
    if isinstance(expression, Multinary):
        return any(expression_requires_dreal(child) for child in expression.children)
    return False


def validate_formula_solver_support(solver, formula):
    if isinstance(formula, Constraint):
        _validate_expression(solver, formula)


def validate_model_solver_support(solver, model):
    validate_formula_solver_support(solver, model.init)
    for expression in model.const_dict.values():
        validate_formula_solver_support(solver, expression)
    for module in model.modules:
        validate_formula_solver_support(solver, module["mode"])
        validate_formula_solver_support(solver, module["inv"])
        _validate_expression(solver, module["flow"])
        for guard, reset in module["jump"].items():
            validate_formula_solver_support(solver, guard)
            validate_formula_solver_support(solver, reset)


def model_requires_dreal(model):
    expressions = [model.init]
    expressions.extend(model.const_dict.values())
    for module in model.modules:
        expressions.extend((module["mode"], module["inv"], module["flow"]))
        for guard, reset in module["jump"].items():
            expressions.extend((guard, reset))
    return any(expression_requires_dreal(expression) for expression in expressions)
