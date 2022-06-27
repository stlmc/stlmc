from functools import singledispatch

from .constraints import *
# making proposition id for each interval ex) [0, tau_0) = p_0, [tau_0, tau_1) = p_1 ...
from .interval import intervalConst, subInterval, inIntervalCheck
from .operations import generate_id

# "new" and "old"
ENC_TYPES = "new"


def baseEncoding(partition: dict, baseCase, time_bound):
    base = {}

    for f in partition.keys():
        if isinstance(f, Bool):
                genProp = generate_id(0, f.id + "_")
                genNotProp = generate_id(0, "not@" + f.id + "_")
                exPar = [RealVal("0.0")] + baseCase + [RealVal(str(time_bound))]
                sub_result = list()
                for i in range(len(baseCase) + 1):
                    sub_result.append((Interval(True, exPar[i], True, exPar[i]), Bool(next(genProp))))
                    sub_result.append((Interval(False, exPar[i], False, exPar[i + 1]), Bool(next(genProp))))
                base[f] = sub_result
                if not "not@" in f.id:
                    base[Bool("not@" + f.id)] = [(Interval(True, exPar[i], False, exPar[i + 1]), Bool(next(genNotProp))) for i
                                         in range(len(baseCase) + 1)]
    return base


def subfMap(formula, fMap):
    if isinstance(formula, Bool):
        if formula in fMap.keys():
            return fMap[formula]
        else:
            return formula
    else:
        subfMap(formula.children, fMap)


def valuation(f: Formula, sub: dict, j: Interval, base: dict):
    genPr = generate_id(0, 'chi')
    fMap = {}

    newSub = {}
    if ENC_TYPES == "old":
        for ns in sub:
            newSub[ns[0]] = sub[ns]
    else:
        newSub = sub
    vf = _value(f, newSub, j, base, genPr, fMap)

    return [vf, *[Eq(pf[0], pf[1]) for pf in fMap.values()]], fMap


@singledispatch
def _value(f: Formula, sub: dict, j: Interval, base, genPr, fMap):
    raise NotImplementedError('Something wrong')


@_value.register(BoolVal)
def _(f: BoolVal, sub: dict, j: Interval, base, genPr, fMap):
    return BoolVal(f.value)


def _value_aux(f: Bool, sub: dict, j: Interval, base, genPr, fMap):
    if f in sub:
        if not (f, j) in fMap:
            np = Bool(next(genPr))
            fMap[(f, j)] = (np, _value(sub[f], sub, j, base, genPr, fMap))
        return fMap[(f, j)][0]
    else:
        return _atomEncoding_old(f, j, base)


def _enhanced_value_aux(f: Bool, sub: dict, j: Interval, base, genPr, fMap):
    if f in base:
        return _atomEncoding(f, j, base)
    for (fkey, time) in sub[1]:
        if isinstance(sub[1][(fkey, time)], Bool):
            if sub[1][(fkey, time)] in base and fkey.id == f.id:
                return _atomEncoding(sub[1][(f, time)], j, base)
    if not (f, j) in fMap:
        for (fkey, time) in sub[1]:
            if fkey.id == f.id:
                np = Bool(next(genPr))
                fMap[(f, j)] = (np, _value(sub[1][(fkey, time)], sub, j, base, genPr, fMap))
                break
    return fMap[(f, j)][0]


@_value.register(Bool)
def _(f: Bool, sub: dict, j: Interval, base, genPr, fMap):
    if ENC_TYPES == "new":
        print("???")
        return _enhanced_value_aux(f, sub, j, base, genPr, fMap)
    elif ENC_TYPES == "old":
        return _value_aux(f, sub, j, base, genPr, fMap)


@_value.register(Not)
def _(f: Not, sub: dict, j: Interval, base, genPr, fMap):
    if f.child in base:
        if ENC_TYPES == "new":
            bound_bool = _atomEncoding(f.child, j, base)
            return Bool("not@" + bound_bool.id)
    return Not(_value(f.child, sub, j, base, genPr, fMap))


@_value.register(Multinary)
def _(f: Multinary, sub: dict, j: Interval, base, genPr, fMap):
    op = {And: And, Or: Or}
    return op[f.__class__]([_value(c, sub, j, base, genPr, fMap) for c in f.children])


@_value.register(Implies)
def _(f: Implies, sub: dict, j: Interval, base, genPr, fMap):
    return Implies(_value(f.left, sub, j, base, genPr, fMap),
                   _value(f.right, sub, j, base, genPr, fMap))


@_value.register(FinallyFormula)
def _(f: FinallyFormula, sub: dict, j: Interval, base, genPr, fMap):
    result = list()
    interval_const = intervalConst(j, f.global_time, f.local_time)
    result.extend(interval_const.children)
    result.append(_value(f.child, sub, f.global_time, base, genPr, fMap))
    return And(result)


@_value.register(GloballyFormula)
def _(f: GloballyFormula, sub: dict, j: Interval, base, genPr, fMap):
    interval_const = intervalConst(j, f.global_time, f.local_time)
    return Implies(interval_const, _value(f.child, sub, f.global_time, base, genPr, fMap))


@_value.register(UntilFormula)
def _(f: UntilFormula, sub: dict, j: Interval, base, genPr, fMap):
    result = list()
    interval_const = intervalConst(j, f.global_time, f.local_time)
    result.extend(interval_const.children)
    result.append(_value(f.left, sub, f.global_time, base, genPr, fMap))
    result.append(_value(f.right, sub, f.global_time, base, genPr, fMap))
    return And(result)


@_value.register(ReleaseFormula)
def _(f: ReleaseFormula, sub: dict, j: Interval, base, genPr, fMap):
    return Or([*[Not(intervalConst(j, f.global_time, f.local_time)),
                 _value(f.left, sub, f.global_time, base, genPr, fMap),
                 _value(f.right, sub, f.global_time, base, genPr, fMap)]])


def _atomEncoding(f: Bool, j: Interval, base: dict):
    for (basePartition, prop) in base[f]:
        if inIntervalCheck(j, basePartition):
            return prop


def _atomEncoding_old(f: Bool, j: Interval, base: dict):
    const = []
    for (basePartition, prop) in base[f]:
        if str(j) == str(basePartition):
            return prop
        const.append(Implies(subInterval(j, basePartition), prop))

    return And(const)
