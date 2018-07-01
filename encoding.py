from formula import *
from const import *
from functools import singledispatch


def baseEncoding(partition:dict, baseCase):
    base = {}
    for f in partition.keys():
        if isinstance(f, PropositionFormula):
            genProp = genId(0, f.id+"_")
            exPar   = [0.0] + baseCase + [float('inf')]
            base[f] = [(Interval(True,exPar[i],False,exPar[i+1]), z3.Bool(next(genProp))) for i in range(len(baseCase)+1)]
    return base


def valuation(f:Formula, sub:dict, j:Interval, base:dict):
    genPr = genId(0, 'chi')
    fMap  = {}
    vf    = _value(f, sub, j, base, genPr, fMap)
    return z3.And([vf] + [pf[0] == pf[1] for pf in fMap.values()])


@singledispatch
def _value(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    raise NotImplementedError('Something wrong')

@_value.register(ConstantFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    return z3.BoolVal(f.getValue())

@_value.register(PropositionFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    if f in sub:
        if not (f,j) in fMap:
            np = z3.Bool(next(genPr))
            fMap[(f,j)] = (np, _value(sub[f], sub, j, base, genPr, fMap))
        return fMap[(f,j)][0]
    else:
        return _atomEncoding(f,j,base)

@_value.register(NotFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    return z3.Not(_value(f.child,sub,j,base,genPr,fMap))

@_value.register(Multiary)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    op = {AndFormula: z3.And, OrFormula: z3.Or}
    return op[f.__class__]([_value(c,sub,j,base,genPr,fMap) for c in f.children])

@_value.register(ImpliesFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    return z3.Implies(_value(f.left,sub,j,base,genPr,fMap), _value(f.right,sub,j,base,genPr,fMap))

@_value.register(FinallyFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    return z3.And([intervalConst(j,f.gtime,f.ltime), _value(f.child,sub,f.gtime,base,genPr,fMap)])

@_value.register(GloballyFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    return z3.Implies(intervalConst(j,f.gtime,f.ltime), _value(f.child,sub,f.gtime,base,genPr,fMap))

@_value.register(UntilFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    return And([intervalConst(j,f.gtime,f.ltime), _value(f.left,sub,f.gtime,base,genPr,fMap), _value(f.right,sub,f.gtime,base,genPr,fMap)])

@_value.register(ReleaseFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap):
    return z3.Or([z3.Not(intervalConst(j,f.gtime,f.ltime)), _value(f.left,sub,f.gtime,base,genPr,fMap), _value(f.right,sub,f.gtime,base,genPr,fMap)])


def _atomEncoding(f:PropositionFormula, j:Interval, base:dict):
    const = []
    for (basePartition,prop) in base[f]:
        const.append(z3.Implies(subInterval(j,basePartition),prop))
    return z3.And(const)


