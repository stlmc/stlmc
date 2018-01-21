
from formula import *
from interval import *
from expr import *
from functools import singledispatch


def valuation(f:Formula, j:Interval):
    genPr = genId(0, 'p')
    fMap  = {}
    vf    = _value(f, j, genPr, fMap)

    return AndConstraint([vf] + [IffConstraint(pf[0], pf[1]) for pf in fMap.values()])

def _cached(key, fMap, genPr, value):
    if not key in fMap:
        np = ConstantConstraint(next(genPr))
        fMap[key] = (np, value)
    return fMap[key][0]

@singledispatch
def _value(f:Formula, j:Interval, genPr, fMap):
    raise NotImplementedError('Something wrong')

@_value.register(ConstantFormula)
def _(f:Formula, j:Interval, genPr, fMap):
    return ConstantConstraint(f.getValue())

@_value.register(PropositionFormula)
def _(f:Formula, j:Interval, genPr, fMap):
    return Atomic((j, f.id))

@_value.register(NotFormula)
def _(f:Formula, j:Interval, genPr, fMap):
    return NegConstraint(_value(f.child,j,genPr,fMap))

@_value.register(Multiary)
def _(f:Formula, j:Interval, genPr, fMap):
    op = {AndFormula: AndConstraint, OrFormula: OrConstraint}
    return op[f.__class__]([_value(c,j,genPr,fMap) for c in f.children])

@_value.register(ImpliesFormula)
def _(f:Formula, j:Interval, genPr, fMap):
    return ImpliesConstraint(_value(f.left,j,genPr,fMap), _value(f.right,j,genPr,fMap))

@_value.register(FinallyFormula)
def _(f:Formula, j:Interval, genPr, fMap):
    f1 = _cached((f.child,f.gtime), fMap, genPr, _value(f.child,f.gtime,genPr,fMap))
    return AndConstraint([_intervalConst(j,f.gtime,f.ltime), f1])

@_value.register(GloballyFormula)
def _(f:Formula, j:Interval, genPr, fMap):
    f1 = _cached((f.child,f.gtime), fMap, genPr, _value(f.child,f.gtime,genPr,fMap))
    return ImpliesConstraint(_intervalConst(j,f.gtime,f.ltime), f1)

@_value.register(UntilFormula)
def _(f:Formula, j:Interval, genPr, fMap):
    f1 = _cached((f.left,f.gtime), fMap, genPr, _value(f.left,f.gtime,genPr,fMap))
    f2 = _cached((f.right,f.gtime), fMap, genPr, _value(f.right,f.gtime,genPr,fMap))
    return AndConstraint([_intervalConst(j,f.gtime,f.ltime), f1, f2])

@_value.register(ReleaseFormula)
def _(f:Formula, j:Interval, genPr, fMap):
    f1 = _cached((f.left,f.gtime), fMap, genPr, _value(f.left,f.gtime,genPr,fMap))
    f2 = _cached((f.right,f.gtime), fMap, genPr, _value(f.right,f.gtime,genPr,fMap))
    return OrConstraint([NegConstraint(_intervalConst(j,f.gtime,f.ltime)), f1, f2])


@singledispatch
def valuationSimple(f:Formula, j:Interval):
    raise NotImplementedError('Something wrong')

@valuationSimple.register(ConstantFormula)
def _(f:Formula, j:Interval):
    return ConstantConstraint(f.getValue())

@valuationSimple.register(PropositionFormula)
def _(f:Formula, j:Interval):
    return Atomic((j, f.id))

@valuationSimple.register(NotFormula)
def _(f:Formula, j:Interval):
    return NegConstraint(valuation(f.child, j))

@valuationSimple.register(Multiary)
def _(f:Formula, j:Interval):
    op = {AndFormula: AndConstraint, OrFormula: OrConstraint}
    return op[f.__class__]([valuation(c, j) for c in f.children])

@valuationSimple.register(ImpliesFormula)
def _(f:Formula, j:Interval):
    return ImpliesConstraint(valuation(f.left, j), valuation(f.right, j))

@valuationSimple.register(FinallyFormula)
def _(f:Formula, j:Interval):
    return AndConstraint([_intervalConst(j,f.gtime,f.ltime), valuation(f.child, f.gtime)])

@valuationSimple.register(GloballyFormula)
def _(f:Formula, j:Interval):
    return ImpliesConstraint(_intervalConst(j,f.gtime,f.ltime), valuation(f.child, f.gtime))

@valuationSimple.register(UntilFormula)
def _(f:Formula, j:Interval):
    return AndConstraint([_intervalConst(j,f.gtime,f.ltime), valuation(f.left, f.gtime), valuation(f.right, f.gtime)])

@valuationSimple.register(ReleaseFormula)
def _(f:Formula, j:Interval):
    return OrConstraint([NegConstraint(_intervalConst(j,f.gtime,f.ltime)), valuation(f.left, f.gtime), valuation(f.right, f.gtime)])


def _intervalConst(j:Interval, k:Interval, i:Interval):
    return Atomic((j, k, i))



