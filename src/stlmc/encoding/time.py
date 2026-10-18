import math

from ..constraints.constraints import And, Eq, Geq, Leq, Lt, Real, RealVal, Sub


def segment_duration_bounds(bound, time_horizon):
    """Bound continuous segments, including STL variable-point splits.

    A bound of zero still contains one segment. Zero-length segments remain
    permitted here; STL/reach ordering supplies its existing strictness rules.
    """
    horizon = float(time_horizon)
    if not math.isfinite(horizon) or horizon < 0:
        raise ValueError("time-horizon must be finite and non-negative")
    if not isinstance(bound, int) or bound < 0:
        raise ValueError("bound must be a non-negative integer")
    children = []
    for index in range(bound + 1):
        duration = Sub(Real("tau_{}".format(index + 1)),
                       Real("tau_{}".format(index)))
        children.extend([
            Geq(duration, RealVal("0")),
            Leq(duration, RealVal(str(horizon))),
        ])
    return And(children)


def make_time_const(bound, time_bound, flag):
    time_const_children = list()
    op_dict = {True: Leq, False: Lt}

    ZenoOperator = op_dict[flag]

    # first constraint
    child_0 = ZenoOperator(RealVal('0'), Real('tau_1'))
    time_const_children.append(child_0)

    for k in range(1, bound):
        time_const_children.append(ZenoOperator(Real('tau_{}'.format(k)), Real('tau_{}'.format(k + 1))))

    child_last = Lt(Real('tau_{}'.format(bound)), RealVal(str(time_bound)))
    time_const_children.append(child_last)

    global_time_limitation = Eq(Real('tau_{}'.format(bound + 1)), RealVal(str(time_bound)))
    time_const_children.append(global_time_limitation)

    return time_const_children


def make_zeno_time_const(bound, time_bound):
    return make_time_const(bound, time_bound, True)


def make_non_zeno_time_const(bound, time_bound):
    return make_time_const(bound, time_bound, False)
