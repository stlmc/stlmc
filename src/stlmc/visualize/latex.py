"""LaTeX rendering for STLmc formulas."""

from functools import singledispatch

from ..constraints.constraints import (
    Add, And, Constant, Div, Eq, FinallyFormula, Formula, Geq,
    GloballyFormula, Gt, Implies, Leq, Lt, Mul, Neq, Not, Or,
    ReleaseFormula, Sqrt, Sub, UntilFormula, Variable,
)
from ..constraints.interval import Interval
from ..exceptions import NotSupportedError


def interval_string(interval: Interval):
    left_end = "[" if interval.left_end else "("
    right_end = "]" if interval.right_end else ")"
    return "{}{},{}{}".format(
        left_end, interval.left, interval.right, right_end
    )


@singledispatch
def formula2latex(formula: Formula):
    raise NotSupportedError("cannot translate formula to latex")


def _binary(formula, operator):
    return "({} {} {})".format(
        formula2latex(formula.left), operator, formula2latex(formula.right)
    )


@formula2latex.register(And)
@formula2latex.register(Or)
def _(formula):
    assert len(formula.children) == 2
    operator = "and" if isinstance(formula, And) else "or"
    return "({} {} {})".format(
        formula2latex(formula.children[0]), operator,
        formula2latex(formula.children[1]),
    )


@formula2latex.register(Implies)
def _(formula: Implies):
    return _binary(formula, "\\rightarrow")


@formula2latex.register(Lt)
def _(formula: Lt):
    return _binary(formula, "<")


@formula2latex.register(Leq)
def _(formula: Leq):
    return _binary(formula, "\\leq")


@formula2latex.register(Gt)
def _(formula: Gt):
    return _binary(formula, ">")


@formula2latex.register(Geq)
def _(formula: Geq):
    return _binary(formula, "\\geq")


@formula2latex.register(Eq)
def _(formula: Eq):
    return _binary(formula, "=")


@formula2latex.register(Neq)
def _(formula: Neq):
    return _binary(formula, "\\neq")


@formula2latex.register(Not)
def _(formula: Not):
    return "(\\neg {})".format(formula2latex(formula.child))


@formula2latex.register(Add)
def _(formula: Add):
    return _binary(formula, "+")


@formula2latex.register(Sub)
def _(formula: Sub):
    return _binary(formula, "-")


@formula2latex.register(Mul)
def _(formula: Mul):
    return _binary(formula, "*")


@formula2latex.register(Div)
def _(formula: Div):
    return _binary(formula, "/")


@formula2latex.register(Sqrt)
def _(formula: Sqrt):
    return "(\\sqrt{{{}}})".format(formula2latex(formula.child))


@formula2latex.register(Variable)
def _(formula: Variable):
    return formula.id


@formula2latex.register(Constant)
def _(formula: Constant):
    return str(formula.value).lower()


@formula2latex.register(UntilFormula)
@formula2latex.register(ReleaseFormula)
def _(formula):
    operator = "U" if isinstance(formula, UntilFormula) else "R"
    return "{} \\mathbf{{{}}}_{{{}}} {}".format(
        formula2latex(formula.left), operator,
        interval_string(formula.local_time), formula2latex(formula.right),
    )


@formula2latex.register(GloballyFormula)
@formula2latex.register(FinallyFormula)
def _(formula):
    operator = "\\square" if isinstance(formula, GloballyFormula) else "\\lozenge"
    return "{}_{{{}}} {}".format(
        operator, interval_string(formula.local_time),
        formula2latex(formula.child),
    )


__all__ = ["formula2latex", "interval_string"]
