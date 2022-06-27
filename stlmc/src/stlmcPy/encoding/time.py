from ..constraints.constraints import *


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
