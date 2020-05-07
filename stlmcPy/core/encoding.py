from .formula import *
from functools import singledispatch
from .interval import *

# making proposition id for each interval ex) [0, tau_0) = p_0, [tau_0, tau_1) = p_1 ...
def baseEncoding(partition:dict, baseCase):
    base = {}
    for f in partition.keys():
        if isinstance(f, PropositionFormula):
            genProp = genId(0, f.id+"_")
            exPar   = [0.0] + baseCase + [float('inf')]
            base[f] = [(Interval(True,exPar[i],False,exPar[i+1]), Bool(next(genProp))) for i in range(len(baseCase)+1)]
    return base

def subfMap(formula, fMap):
    if isinstance(formula, PropositionFormula):
        if formula in fMap.keys():
            return fMap[formula]
        else:
            return formula
    else:
        subfMap(formula.children, fMap)

def valuation(f:Formula, sub:dict, j:Interval, base:dict):
    genPr = genId(0, 'chi')
    fMap  = {}
    subFormula = {}
    subFormulaFOL = dict()
    for k in sub.keys():
        subFormulaFOL[k] = _subformulaMap(sub[k], sub, j, base, genPr, fMap, subFormula)
       
    vf    = _value(f, sub, j, base, genPr, fMap, subFormulaFOL)

    return (And(vf, *[pf[0] == pf[1] for pf in fMap.values()]), fMap)


@singledispatch
def _subformulaMap(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    raise NotImplementedError('Something wrong')

@_subformulaMap.register(ConstantFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    return BoolVal(f.getValue())

@_subformulaMap.register(PropositionFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    if f in sub:
        if not (f,j) in fMap:
            np = Bool(next(genPr))
            fMap[(f,j)] = (np, _value(sub[f], sub, j, base, genPr, fMap, subFormula))
        return fMap[(f,j)][0]
    for k in subFormula.keys():
        if str(f) == str(k):
            return subFormula[k]
    else:
        return _atomEncoding(f,j,base)

@_subformulaMap.register(NotFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    for k in subFormula.keys():
        if str(f) == str(k):
            return subFormula[k]
    subFormula[f] = Not(_subformulaMap(f.child,sub,j,base,genPr,fMap, subFormula))
    return subFormula[f] 

@_subformulaMap.register(Multiary)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    op = {AndFormula: And, OrFormula: Or}
    formulas = []
    for c in f.children:
        enter = False
        for k in subFormula.keys():
            if str(c) == str(k):
                enter = True
                formulas.append(k)
        if not enter:
            subFormula[c] = _subformulaMap(c,sub,j,base,genPr,fMap, subFormula)
            formulas.append(subFormula[c])
    return op[f.__class__](*formulas)

@_subformulaMap.register(ImpliesFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    for k in subFormula.keys():
        if str(f) == str(k):
            return subFormula[k]
    subFormula[f] = Implies(_subformulaMap(f.left,sub,j,base,genPr,fMap, subFormula), _subformulaMap(f.right,sub,j,base,genPr,fMap, subFormula))
    subFormula[f.left] = _subformulaMap(f.left,sub,j,base,genPr,fMap, subFormula)
    subFormula[f.right] = _subformulaMap(f.right,sub,j,base,genPr,fMap, subFormula)
    return subFormula[f] 

@_subformulaMap.register(FinallyFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    for k in subFormula.keys():
        if str(f) == str(k):
            return subFormula[k]
    args = [intervalConst(j,f.gtime,f.ltime), _subformulaMap(f.child,sub,f.gtime,base,genPr,fMap, subFormula)]
    subFormula[f] = And(*args)
    return subFormula[f]

@_subformulaMap.register(GloballyFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    for k in subFormula.keys():
        if str(f) == str(k):
            return subFormula[k]
    subFormula[f] = Implies(intervalConst(j,f.gtime,f.ltime), _subformulaMap(f.child,sub,f.gtime,base,genPr,fMap, subFormula)) 
    return subFormula[f]

@_subformulaMap.register(UntilFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    for k in subFormula.keys():
        if str(f) == str(k):
            return subFormula[k]
    subFormula[f] = And(*[intervalConst(j,f.gtime,f.ltime), _subformulaMap(f.left,sub,f.gtime,base,genPr,fMap, subFormula), _subformulaMap(f.right,sub,f.gtime,base,genPr,fMap, subFormula)])
    return subFormula[f]

@_subformulaMap.register(ReleaseFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    for k in subFormula.keys():
        if str(f) == str(k):
            return subFormula[k]
    subFormula[f] = Or(*[Not(intervalConst(j,f.gtime,f.ltime)), _subformulaMap(f.left,sub,f.gtime,base,genPr,fMap, subFormula), _subformulaMap(f.right,sub,f.gtime,base,genPr,fMap, subFormula)])
    return subFormula[f]

@singledispatch
def _value(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    raise NotImplementedError('Something wrong')

@_value.register(ConstantFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula): 
    return BoolVal(f.getValue())

@_value.register(PropositionFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    for k in subFormula.keys():
        if str(f) == str(k):
            return subFormula[k]
    if f in sub:
        if not (f,j) in fMap:
            np = Bool(next(genPr))
            fMap[(f,j)] = (np, _value(sub[f], sub, j, base, genPr, fMap, subFormula))
        return fMap[(f,j)][0]
    else:
        return _atomEncoding(f,j,base)

@_value.register(NotFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    #subFormula[f.child] = Not(_value(f.child,sub,j,base,genPr,fMap, subFormula))
    return Not(_value(f.child,sub,j,base,genPr,fMap, subFormula))

@_value.register(Multiary)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    op = {AndFormula: And, OrFormula: Or}
    #for c in f.children:
    #    subFormula[c] = _value(c,sub,j,base,genPr,fMap, subFormula)
    return op[f.__class__](*[_value(c,sub,j,base,genPr,fMap, subFormula) for c in f.children])

@_value.register(ImpliesFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    #subFormula[f.left] = _value(f.left,sub,j,base,genPr,fMap, subFormula)
    #subFormula[f.right] = _value(f.right,sub,j,base,genPr,fMap, subFormula)
    return Implies(_value(f.left,sub,j,base,genPr,fMap, subFormula), _value(f.right,sub,j,base,genPr,fMap, subFormula))

@_value.register(FinallyFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
#    subFormula[f.child] = _value(f.child,sub,f.gtime,base,genPr,fMap, subFormula)
    args = [intervalConst(j,f.gtime,f.ltime), _value(f.child,sub,f.gtime,base,genPr,fMap, subFormula)]
    return And(*args)

@_value.register(GloballyFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
#    subFormula[f.child] = _value(f.child,sub,f.gtime,base,genPr,fMap, subFormula)
    return Implies(intervalConst(j,f.gtime,f.ltime), _value(f.child,sub,f.gtime,base,genPr,fMap, subFormula))

@_value.register(UntilFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    return And(*[intervalConst(j,f.gtime,f.ltime), _value(f.left,sub,f.gtime,base,genPr,fMap, subFormula), _value(f.right,sub,f.gtime,base,genPr,fMap, subFormula)])

@_value.register(ReleaseFormula)
def _(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
    return Or(*[Not(intervalConst(j,f.gtime,f.ltime)), _value(f.left,sub,f.gtime,base,genPr,fMap, subFormula), _value(f.right,sub,f.gtime,base,genPr,fMap, subFormula)])


def _atomEncoding(f:PropositionFormula, j:Interval, base:dict):
    const = []
    for (basePartition,prop) in base[f]:
        const.append(Implies(subInterval(j,basePartition),prop))
    return And(*const)

@singledispatch
def _substitution(f:Formula, sub:dict):
    raise NotImplementedError('Something wrong')


@_substitution.register(PropositionFormula)
def _(f:Formula, sub:dict):
    if f in sub.keys():
        return sub[f]
    else:
        return f

@_substitution.register(NotFormula)
def _(f:Formula, sub:dict):
    return Not(_substitution(f.child, sub))

@_substitution.register(Multiary)
def _(f:Formula, sub:dict):
    op = {AndFormula: And, OrFormula: Or}
    return op[f.__class__](*[_substitution(c,sub) for c in f.children])

@_substitution.register(ImpliesFormula)
def _(f:Formula, sub:dict):
    return Implies(_substitution(f.left,sub), _substitution(f.right,sub))

@_substitution.register(FinallyFormula)
def _(f:Formula, sub:dict):
    return FinallyFormula(f.ltime,f.gtime, _substitution(f.child,sub))

@_substitution.register(GloballyFormula)
def _(f:Formula, sub:dict):
    return GloballyFormula(f.ltime,f.gtime, _substitution(f.child,sub))

@_substitution.register(UntilFormula)
def _(f:Formula, sub:dict):
    return UntilFormula(f.ltime,f.gtime, _substitution(f.left,sub), _substitution(f.right,sub))

@_substitution.register(ReleaseFormula)
def _(f:Formula, sub:dict):
    return ReleaseFormula(f.ltime,f.gtime, _substitution(f.left,sub), _substitution(f.right,sub))






