from .constraints import *
from functools import singledispatch


# making proposition id for each interval ex) [0, tau_0) = p_0, [tau_0, tau_1) = p_1 ...
from .interval import intervalConst, subInterval, inIntervalCheck
from .operations import generate_id


def baseEncoding(partition: dict, baseCase):
    base = {}

    for f in partition.keys():
        if isinstance(f, Bool):
            genProp = generate_id(0, f.id + "_")
            exPar = [0.0] + baseCase + [float('inf')]
            base[f] = [(Interval(True, exPar[i], False, exPar[i + 1]), Bool(next(genProp))) for i in
                       range(len(baseCase) + 1)]
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
    subFormula = {}
    subFormulaFOL = dict()

    vf = _value(f, sub, j, base, genPr, fMap, subFormulaFOL)

    return And([vf, *[Eq(pf[0], pf[1]) for pf in fMap.values()]]), fMap


@singledispatch
def _value(f: Formula, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    raise NotImplementedError('Something wrong')


@_value.register(BoolVal)
def _(f: BoolVal, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    return BoolVal(f.value)


@_value.register(Bool)
def _(f: Bool, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    '''
    print("what is sub")
    print(sub)
    print("what is base")
    print(base)
    print(f)
    print("==========")
    '''
    if f in base:
        return _atomEncoding(f, j, base)
    if f in sub:
        if sub[f] in base:
            return _atomEncoding(sub[f], j, base)
    if f in sub:
        if not (f, j) in fMap:
            np = Bool(next(genPr))
            fMap[(f, j)] = (np, _value(sub[f], sub, j, base, genPr, fMap, subFormula))
        return fMap[(f, j)][0]


@_value.register(Not)
def _(f: Not, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    return Not(_value(f.child, sub, j, base, genPr, fMap, subFormula))


@_value.register(Multinary)
def _(f: Multinary, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    op = {And: And, Or: Or}
    return op[f.__class__]([_value(c, sub, j, base, genPr, fMap, subFormula) for c in f.children])


@_value.register(Implies)
def _(f: Implies, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    return Implies(_value(f.left, sub, j, base, genPr, fMap, subFormula),
                   _value(f.right, sub, j, base, genPr, fMap, subFormula))


@_value.register(FinallyFormula)
def _(f: FinallyFormula, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    args = [intervalConst(j, f.global_time, f.local_time), _value(f.child, sub, f.global_time, base, genPr, fMap, subFormula)]
    return And(args)


@_value.register(GloballyFormula)
def _(f: GloballyFormula, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    return Implies(intervalConst(j, f.global_time, f.local_time), _value(f.child, sub, f.global_time, base, genPr, fMap, subFormula))


@_value.register(UntilFormula)
def _(f: UntilFormula, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    return And([*[intervalConst(j, f.global_time, f.local_time), _value(f.left, sub, f.global_time, base, genPr, fMap, subFormula),
                 _value(f.right, sub, f.global_time, base, genPr, fMap, subFormula)]])


@_value.register(ReleaseFormula)
def _(f: ReleaseFormula, sub: dict, j: Interval, base, genPr, fMap, subFormula):
    return Or([*[Not(intervalConst(j, f.global_time, f.local_time)), _value(f.left, sub, f.global_time, base, genPr, fMap, subFormula),
                _value(f.right, sub, f.global_time, base, genPr, fMap, subFormula)]])


def _atomEncoding(f: Bool, j: Interval, base: dict):
    for (basePartition, prop) in base[f]:
        if inIntervalCheck(j, basePartition):
            return prop





