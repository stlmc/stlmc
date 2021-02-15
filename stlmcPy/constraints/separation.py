from .constraints import *
from functools import singledispatch
from .interval import *


def fullSeparation(index, subFormula, var_point, var_interval, id_match_dict):
    result = list()
    chi_list = [str(c) for c in list(id_match_dict.values())]
    max = 0
    for c in chi_list:
        if "chi_" in c:
            if int(c[c.find("_") + 1:]) > max:
                max = int(c[c.find("_") + 1:])

    if not isinstance(subFormula, Bool):
        for i in range(len(var_point)):
            result.append(Eq(Bool("chi_" + str(index) + "_" + str(i + 1)),
                             _separation(subFormula, i + 1, var_point, var_interval, id_match_dict)))
            if index == max:
                break
    return result


def make_time_list(bound):
    var_point = list()
    var_interval = list()
    for i in range(bound):
        if i == 0:
            # var_point.append(RealVal("0"))
            # var_interval.append(Interval(True, RealVal("0"), True, RealVal("0")))
            point = Real("tau_" + str(i + 1))
            var_point.append(point / RealVal("2"))
            var_interval.append(Interval(True, RealVal("0"), False, point))
        # var_point.append(point)
        # var_interval.append(Interval(True, point, True, point))
        else:
            start = Real("tau_" + str(i))
            end = Real("tau_" + str(i + 1))
            var_point.append((start + end) / RealVal("2"))
            # var_point.append(end)
            var_interval.append(Interval(True, start, False, end))
        # var_interval.append(Interval(True, end, True, end))
    var_point.append((Real("tau_" + str(bound)) + Real("tau_" + str(bound + 1))) / RealVal("2"))
    var_interval.append(Interval(True, Real("tau_" + str(bound)), False, Real("tau_" + str(bound + 1))))

    return var_point, var_interval


# v : [0, (tau_1)/2, (tau_1 + tau_2) / 2, ...]
# j : [{0}, (0, tau_1), {tau_1}, (tau_1, tau_2), ....]
@singledispatch
def _separation(f: Formula, i, v, j, idDict):
    raise NotImplementedError('Something wrong')


@_separation.register(Bool)
def _(f: Bool, i, v, j, idDict):
    str_id = f.id + "_" + str(i - 1)
    return Bool(str_id)


@_separation.register(Constant)
def _(f: Constant, i, v, j, idDict):
    return f


@_separation.register(Not)
def _(f: Not, i, v, j, idDict):
    if not "chi" in idDict[f.child].id:
        str_id = idDict[f.child].id + "_" + str(i - 1)
        return Bool(str_id)
    return Not(Bool(idDict[f.child].id + "_" + str(i)))


@_separation.register(Multinary)
def _(f: Multinary, i, v, j, idDict):
    flatten = list()
    ft = f.__class__
    result = [_separation(c, i, v, j, idDict) for c in f.children]
    for r in result:
        if isinstance(r, ft):
            flatten.extend(r.children)
        else:
            flatten.append(r)
    return f.__class__(flatten)


@_separation.register(Implies)
def _(f: Implies, i, j, idDict):
    return f.__class__(_separation(f.left, i, v, j, idDict), _separation(f.right, i, v, j, idDict))


@_separation.register(BinaryTemporalFormula)
def _(f: BinaryTemporalFormula, i, v, j, idDict):
    return _trans(f, i, i, v, j, idDict)


@_separation.register(UnaryTemporalFormula)
def _(f: UnaryTemporalFormula, i, v, j, idDict):
    return _trans(f, i, i, v, j, idDict)


@singledispatch
def _trans(f: Formula, i, k, v, j, idDict):
    print(type(f))
    print(f)

    raise NotImplementedError('Something wrong')


@_trans.register(UntilFormula)
def _(f: UntilFormula, i, k, v, j, idDict):
    if k >= (len(j) + 1):
        return BoolVal("False")
    and_chi = list()
    and_chi.extend(inInterval(v[i - 1], minusInterval(j[k - 1], f.local_time)).children)
    if "chi" in idDict[f.left].id:
        left_ind = k
    else:
        left_ind = int((k - 1) / 2)
    if "chi" in idDict[f.right].id:
        right_ind = k
    else:
        right_ind = int((k - 1) / 2)
    and_chi.append(Bool(idDict[f.left].id + "_" + str(left_ind)))
    and_chi.append(Bool(idDict[f.right].id + "_" + str(right_ind)))
    return Or([And(and_chi), And([Bool(idDict[f.left].id + "_" + str(left_ind)), _trans(f, i, k + 1, v, j, idDict)])])


@_trans.register(ReleaseFormula)
def _(f: ReleaseFormula, i, k, v, j, idDict):
    if k >= (len(j) + 1):
        return BoolVal("True")
    and_chi = list()
    and_chi.append(Not(inInterval(v[i - 1], minusInterval(j[k - 1], f.local_time))))
    if "chi" in idDict[f.left].id:
        left_ind = k
    else:
        left_ind = int((k - 1) / 2)
    if "chi" in idDict[f.right].id:
        right_ind = k
    else:
        right_ind = int((k - 1) / 2)
    and_chi.append(Bool(idDict[f.left].id + "_" + str(left_ind)))
    and_chi.append(Bool(idDict[f.right].id + "_" + str(right_ind)))
    return And([Or(and_chi), Or([Bool(idDict[f.left].id + "_" + str(left_ind)), _trans(f, i, k + 1, v, j, idDict)])])


@_trans.register(FinallyFormula)
def _(f: FinallyFormula, i, k, v, j, idDict):
    if k >= (len(j) + 1):
        return BoolVal("False")
    and_chi = list()
    and_chi.extend(inInterval(v[i - 1], minusInterval(j[k - 1], f.local_time)).children)

    if "chi" in idDict[f.child].id:
        ind = k
    else:
        ind = int((k - 1) / 2)
    and_chi.append(Bool(idDict[f.child].id + "_" + str(ind)))
    return Or([And(and_chi), _trans(f, i, k + 1, v, j, idDict)])


@_trans.register(GloballyFormula)
def _(f: GloballyFormula, i, k, v, j, idDict):
    if k >= (len(j) + 1):
        return BoolVal("True")
    and_chi = list()
    and_chi.append(Not(inInterval(v[i - 1], minusInterval(j[k - 1], f.local_time))))
    if "chi" in idDict[f.child].id:
        ind = k
    else:
        ind = int((k - 1) / 2)
    and_chi.append(Bool(idDict[f.child].id + "_" + str(ind)))
    return And([Or(and_chi), _trans(f, i, k + 1, v, j, idDict)])


@_trans.register(Not)
def _(f: Not, i, k, v, j, idDict):
    return Not(_trans(f.child, i, k, v, j, idDict))
