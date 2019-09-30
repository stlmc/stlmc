from .formula import *
from functools import singledispatch

@singledispatch
def _substitution(f:Formula, sub:dict, j:Interval, base, genPr, fMap, subFormula):
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
def _(f:Formula, sub:dict)
    return GloballyFormula(f.ltime,f.gtime, _substitution(f.child,sub))

@_substitution.register(UntilFormula)
def _(f:Formula, sub:dict):
    return UntilFormula(f.ltime,f.gtime, _substitution(f.left,sub), _substitution(f.right,sub))

@_substitution.register(ReleaseFormula)
def _(f:Formula, sub:dict):
    return ReleaseFormula(f.ltime,f.gtime, _substitution(f.left,sub), _substitution(f.right,sub))

