
from formula import *
from const import *
from functools import singledispatch


def baseEncoding(partition:dict):
    base = {}
    for (f,par) in partition.items():
        if isinstance(f, PropositionFormula):
            genProp = genId(0, "#" + f.id)
            exPar   = [0.0] + par + [float('inf')]
            base[f] = [(Interval(True,exPar[i],False,exPar[i+1]), Bool(next(genProp))) for i in range(len(par)+1)]
    return base


def valuation(f:Formula, base:dict, j:Interval):
    genPr = genId(0, 'chi')
    fMap  = {}
    vf    = _value(f, j, genPr, fMap, base)
    return And([vf] + [pf[0] == pf[1] for pf in fMap.values()])


def _cached(key, fMap, genPr, valueFunc):
    if not key in fMap:
        np = Bool(next(genPr))
        fMap[key] = (np, valueFunc())
    return fMap[key][0]


def _atomEncoding(f:PropositionFormula, j:Interval, base:dict):
    const = []
    for (basePartition,prop) in base[f]:
        const.append(Implies(subInterval(j,basePartition),prop))
    return And(const)


@singledispatch
def _value(f:Formula, j:Interval, genPr, fMap, base):
    raise NotImplementedError('Something wrong')

@_value.register(ConstantFormula)
def _(f:Formula, j:Interval, genPr, fMap, base):
    return BoolVal(f.getValue())

@_value.register(PropositionFormula)
def _(f:Formula, j:Interval, genPr, fMap, base):
    return _cached((f,j), fMap, genPr, lambda: _atomEncoding(f,j,base))

@_value.register(NotFormula)
def _(f:Formula, j:Interval, genPr, fMap, base):
    return Not(_value(f.child,j,genPr,fMap,base))

@_value.register(Multiary)
def _(f:Formula, j:Interval, genPr, fMap, base):
    op = {AndFormula: And, OrFormula: Or}
    return op[f.__class__]([_value(c,j,genPr,fMap,base) for c in f.children])

@_value.register(ImpliesFormula)
def _(f:Formula, j:Interval, genPr, fMap, base):
    return Implies(_value(f.left,j,genPr,fMap,base), _value(f.right,j,genPr,fMap,base))

@_value.register(FinallyFormula)
def _(f:Formula, j:Interval, genPr, fMap, base):
    f1 = _cached((f.child,f.gtime), fMap, genPr, lambda: _value(f.child,f.gtime,genPr,fMap,base))
    return And([intervalConst(j,f.gtime,f.ltime), f1])

@_value.register(GloballyFormula)
def _(f:Formula, j:Interval, genPr, fMap, base):
    f1 = _cached((f.child,f.gtime), fMap, genPr, lambda: _value(f.child,f.gtime,genPr,fMap,base))
    return Implies(intervalConst(j,f.gtime,f.ltime), f1)

@_value.register(UntilFormula)
def _(f:Formula, j:Interval, genPr, fMap, base):
    f1 = _cached((f.left,f.gtime), fMap, genPr, lambda: _value(f.left,f.gtime,genPr,fMap,base))
    f2 = _cached((f.right,f.gtime), fMap, genPr, lambda: _value(f.right,f.gtime,genPr,fMap,base))
    return And([intervalConst(j,f.gtime,f.ltime), f1, f2])

@_value.register(ReleaseFormula)
def _(f:Formula, j:Interval, genPr, fMap, base):
    f1 = _cached((f.left,f.gtime), fMap, genPr, lambda: _value(f.left,f.gtime,genPr,fMap,base))
    f2 = _cached((f.right,f.gtime), fMap, genPr, lambda: _value(f.right,f.gtime,genPr,fMap,base))
    return Or([Not(intervalConst(j,f.gtime,f.ltime)), f1, f2])


@singledispatch
def valuationSimple(f:Formula, j:Interval):
    raise NotImplementedError('Something wrong')

@valuationSimple.register(ConstantFormula)
def _(f:Formula, j:Interval):
    return RealVal(f.getValue())

@valuationSimple.register(PropositionFormula)
def _(f:Formula, j:Interval):
    return Atomic((j, f.id))

@valuationSimple.register(NotFormula)
def _(f:Formula, j:Interval):
    return Not(valuation(f.child, j))

@valuationSimple.register(Multiary)
def _(f:Formula, j:Interval):
    op = {AndFormula: And, OrFormula: Or}
    return op[f.__class__]([valuation(c, j) for c in f.children])

@valuationSimple.register(ImpliesFormula)
def _(f:Formula, j:Interval):
    return Implies(valuation(f.left, j), valuation(f.right, j))

@valuationSimple.register(FinallyFormula)
def _(f:Formula, j:Interval):
    return And([intervalConst(j,f.gtime,f.ltime), valuation(f.child, f.gtime)])

@valuationSimple.register(GloballyFormula)
def _(f:Formula, j:Interval):
    return Implies(intervalConst(j,f.gtime,f.ltime), valuation(f.child, f.gtime))

@valuationSimple.register(UntilFormula)
def _(f:Formula, j:Interval):
    return And([intervalConst(j,f.gtime,f.ltime), valuation(f.left, f.gtime), valuation(f.right, f.gtime)])

@valuationSimple.register(ReleaseFormula)
def _(f:Formula, j:Interval):
    return Or([Not(intervalConst(j,f.gtime,f.ltime)), valuation(f.left, f.gtime), valuation(f.right, f.gtime)])
