from stlmcPy.constraints.constraints import Leq, Lt, Real, RealVal, Eq, Sub, Add


def make_time_const(bound, time_bound, flag, is_delta_set, delta):
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

    # delta relaxing if set
    if is_delta_set:
        print("dddeltaaa")
        tb = RealVal(str(time_bound))
        _delta = RealVal(str(delta))
        lb_tb = Sub(tb, _delta)
        up_tb = Add(tb, _delta)
        last_tau = Real('tau_{}'.format(bound + 1))
        time_const_children.append(Leq(lb_tb, last_tau))
        time_const_children.append(Leq(last_tau, up_tb))
    else:
        # else, do nothing
        global_time_limitation = Eq(Real('tau_{}'.format(bound + 1)), RealVal(str(time_bound)))
        time_const_children.append(global_time_limitation)

    return time_const_children


def make_zeno_time_const(bound, time_bound, is_delta_set, delta):
    return make_time_const(bound, time_bound, True, is_delta_set, delta)


def make_non_zeno_time_const(bound, time_bound, is_delta_set, delta):
    return make_time_const(bound, time_bound, False, is_delta_set, delta)
