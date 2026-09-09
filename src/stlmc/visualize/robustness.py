"""Quantitative robustness evaluation over sampled bounded traces."""

from functools import singledispatch
from typing import Dict, List, Tuple

import sympy

from ..constraints.constraints import (
    And, Bool, BoolVal, Constraint, Eq, FinallyFormula, Formula, Geq,
    GloballyFormula, Gt, Implies, Leq, Lt, Not, Or, Real, RealVal,
    ReleaseFormula, UntilFormula, Variable,
)
from ..constraints.analysis import get_vars
from ..constraints.formatting import infix
from ..constraints.substitution import substitution
from ..constraints.robustness import release_robustness, until_robustness
from ..exceptions import NotSupportedError
from .sampling import get_sub_time_samples

@singledispatch
def robustness(const: Constraint, point_samples: Dict[Variable, List[List[float]]],
               discrete_samples: Dict[Variable, List[List[float]]],
               time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Bool)
def _(const: Bool, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    if const not in discrete_samples:
        raise NotSupportedError(
            "cannot find discrete samples for a Boolean proposition \"{}\""
            .format(const)
        )
    for interval_index, time_samples in enumerate(times):
        for index, sample_time in enumerate(time_samples):
            if sample_time != time:
                continue
            truth_value = discrete_samples[const][interval_index][index]
            robust_value = (
                float("inf") if truth_value > 0
                else float("-inf") if truth_value < 0
                else 0.0
            )
            dp_table[(const, time)] = robust_value
            return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Implies)
def _(const: Implies, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    robust_value = robustness(Or([Not(const.left), const.right]), point_samples, discrete_samples, time, times,
                              time_max, dp_table)
    dp_table[(const, time)] = robust_value
    return robust_value

@robustness.register(BoolVal)
def _(const: BoolVal, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    if const.value == "True":
        robust_value = float("inf")
        dp_table[(const, time)] = robust_value
        return robust_value
    if const.value == "False":
        robust_value = float("-inf")
        dp_table[(const, time)] = robust_value
        return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Eq)
def _(const: Eq, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    return robustness(And([Leq(const.left, const.right),Geq(const.left, const.right)]), 
                      point_samples, discrete_samples, time, times, time_max, dp_table)


@robustness.register(Geq)
def _(const: Geq, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    lhs = const.left - const.right
    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Real, RealVal] = dict()
                for v in point_samples:
                    substitute_dict[v] = RealVal(str(point_samples[v][interval_index][index]))
                expr = substitution(lhs, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, time)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Gt)
def _(const: Gt, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    lhs = const.left - const.right
    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Real, RealVal] = dict()
                for v in point_samples:
                    substitute_dict[v] = RealVal(str(point_samples[v][interval_index][index]))
                expr = substitution(lhs, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, time)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Leq)
def _(const: Leq, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    lhs = const.right - const.left
    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Real, RealVal] = dict()
                for v in point_samples:
                    substitute_dict[v] = RealVal(str(point_samples[v][interval_index][index]))
                expr = substitution(lhs, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, time)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Lt)
def _(const: Lt, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    lhs = const.right - const.left
    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Real, RealVal] = dict()
                for v in point_samples:
                    substitute_dict[v] = RealVal(str(point_samples[v][interval_index][index]))
                expr = substitution(lhs, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, time)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Not)
def _(const: Not, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    robust_value = - robustness(const.child, point_samples, discrete_samples, time, times, time_max, dp_table)
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(And)
def _(const: And, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    robust_value = min(
        [robustness(c, point_samples, discrete_samples, time, times, time_max, dp_table) for c in const.children])
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(Or)
def _(const: Or, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    robust_value = max(
        [robustness(c, point_samples, discrete_samples, time, times, time_max, dp_table) for c in const.children])
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(UntilFormula)
def _(const: UntilFormula, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    intv_left = float(str(sympy.parse_expr(const.local_time.left.value, evaluate=True)))
    intv_right = float(str(sympy.parse_expr(const.local_time.right.value, evaluate=True)))

    t_primes = get_sub_time_samples(times, time + intv_left, time + intv_right, time_max)

    robust_value = until_robustness(
        t_primes,
        lambda witness: get_sub_time_samples(
            times, time, witness, time_max
        ),
        lambda sample: robustness(
            const.left, point_samples, discrete_samples, sample,
            times, time_max, dp_table
        ),
        lambda witness: robustness(
            const.right, point_samples, discrete_samples, witness,
            times, time_max, dp_table
        ),
    )

    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(ReleaseFormula)
def _(const: ReleaseFormula, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    intv_left = float(str(sympy.parse_expr(const.local_time.left.value, evaluate=True)))
    intv_right = float(str(sympy.parse_expr(const.local_time.right.value, evaluate=True)))

    t_primes = get_sub_time_samples(times, time + intv_left, time + intv_right, time_max)
    robust_value = release_robustness(
        t_primes,
        lambda witness: get_sub_time_samples(
            times, time, witness, time_max
        ),
        lambda sample: robustness(
            const.left, point_samples, discrete_samples, sample,
            times, time_max, dp_table
        ),
        lambda witness: robustness(
            const.right, point_samples, discrete_samples, witness,
            times, time_max, dp_table
        ),
    )
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(GloballyFormula)
def _(const: GloballyFormula, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    intv_left = float(str(sympy.parse_expr(const.local_time.left.value, evaluate=True)))
    intv_right = float(str(sympy.parse_expr(const.local_time.right.value, evaluate=True)))

    t_primes = get_sub_time_samples(times, time + intv_left, time + intv_right, time_max)
    robust_value = min(
        (robustness(const.child, point_samples, discrete_samples, t_prime,
                    times, time_max, dp_table) for t_prime in t_primes),
        default=float("inf"),
    )
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(FinallyFormula)
def _(const: FinallyFormula, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    intv_left = float(str(sympy.parse_expr(const.local_time.left.value, evaluate=True)))
    intv_right = float(str(sympy.parse_expr(const.local_time.right.value, evaluate=True)))

    t_primes = get_sub_time_samples(times, time + intv_left, time + intv_right, time_max)
    robust_value = max(
        (robustness(const.child, point_samples, discrete_samples, t_prime,
                    times, time_max, dp_table) for t_prime in t_primes),
        default=float("-inf"),
    )
    dp_table[(const, time)] = robust_value
    return robust_value

__all__ = ["robustness"]
