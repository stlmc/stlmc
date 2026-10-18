"""Exact elimination of time from Boolean flow conditions when supported."""

from .constraints import (
    Add, And, Bool, BoolVal, Div, Eq, Function, Geq, Gt, Int, IntVal,
    Leq, Lt, Mul, Neg, Not, Ode, Or, Pow, Real, RealVal, Sub,
)
from .analysis import get_vars
from .substitution import substitution
from ..exceptions import NotSupportedError


def flow_condition_at_time(forall, elapsed):
    """Instantiate a flow condition at a symbolic local elapsed time."""
    integral = forall.integral
    dynamics = integral.dynamics
    mapping = {}
    if isinstance(dynamics, Function):
        clock_mapping = {
            forall.end_tau: Add(forall.start_tau, elapsed),
        }
        for variable, expression in zip(integral.start_vector, dynamics.exps):
            mapping[variable] = substitution(expression, clock_mapping)
    elif isinstance(dynamics, Ode):
        states = set(integral.start_vector) | set(dynamics.vars)
        for variable, expression in zip(integral.start_vector, dynamics.exps):
            if get_vars(expression) & states or any(
                    v.id.startswith("tau_") or v.id == "time"
                    for v in get_vars(expression)):
                raise NotSupportedError(
                    "OR invariant requires a closed-form flow or a "
                    "state-independent autonomous ODE"
                )
            mapping[variable] = Add(variable, Mul(elapsed, expression))
    else:
        raise NotSupportedError("unsupported flow for OR invariant")

    return substitution(forall.const, mapping)


def eliminate_boolean_flow_condition(forall):
    """Eliminate time for backends that cannot accept the quantifier."""
    try:
        import z3
        from ..solver.z3 import z3Obj
    except Exception as error:
        from ..exceptions import SolverUnavailableError
        raise SolverUnavailableError(
            "Z3 is required to eliminate this Boolean flow invariant. "
            "Run: stlmc-installer install --solver z3"
        ) from error

    duration = z3Obj(Sub(forall.end_tau, forall.start_tau))
    time = z3.FreshReal("stlmc_flow_time")
    body = z3Obj(flow_condition_at_time(forall, Real(time.decl().name())))
    # Invariant starts are checked separately by the model encoding.
    query = z3.ForAll([time], z3.Implies(
        z3.And(time > 0, time < duration), body,
    ))
    result = z3.Tactic("qe")(query).as_expr()

    def convert(term):
        if z3.is_quantifier(term):
            raise NotSupportedError("cannot eliminate time from OR invariant")
        if z3.is_true(term) or z3.is_false(term):
            return BoolVal(str(z3.is_true(term)))
        if z3.is_rational_value(term):
            numerator = RealVal(str(term.numerator_as_long()))
            denominator = term.denominator_as_long()
            return numerator if denominator == 1 else Div(
                numerator, RealVal(str(denominator)))
        if z3.is_int_value(term):
            return IntVal(str(term.as_long()))
        kind = term.decl().kind()
        children = [convert(child) for child in term.children()]
        if kind == z3.Z3_OP_UNINTERPRETED and not children:
            types = {z3.Z3_BOOL_SORT: Bool, z3.Z3_INT_SORT: Int,
                     z3.Z3_REAL_SORT: Real}
            return types[term.sort().kind()](term.decl().name())
        if kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
            return (And if kind == z3.Z3_OP_AND else Or)(children)
        unary = {z3.Z3_OP_NOT: Not, z3.Z3_OP_UMINUS: Neg}
        if kind in unary:
            return unary[kind](children[0])
        if kind == z3.Z3_OP_TO_REAL:
            return children[0]
        binary = {z3.Z3_OP_EQ: Eq, z3.Z3_OP_LE: Leq, z3.Z3_OP_LT: Lt,
                  z3.Z3_OP_GE: Geq, z3.Z3_OP_GT: Gt, z3.Z3_OP_ADD: Add,
                  z3.Z3_OP_SUB: Sub, z3.Z3_OP_MUL: Mul,
                  z3.Z3_OP_DIV: Div, z3.Z3_OP_POWER: Pow}
        if kind not in binary:
            raise NotSupportedError("unsupported eliminated invariant: {}".format(term))
        value = children[0]
        for child in children[1:]:
            value = binary[kind](value, child)
        return value

    return And([
        Eq(Real("currentMode_{}".format(int(forall.end_tau.id[4:]) - 1)),
           RealVal(str(forall.current_mode_number))),
        convert(result),
    ])
