
from formula import *
from interval import *
from expr import *


def valuation(f:Formula, j:Interval):
    genPr = genId(0, 'p')
    fMap  = {}
    vf    = _valuation(f, j, genPr, fMap)

    return AndConstraint([vf] + [IffConstraint(pf[0], pf[1]) for pf in fMap.values()])



def _valuation(f:Formula, j:Interval, genPr, fMap):
    if isinstance(f, ConstantFormula):
        return ConstantConstraint(f.getValue())
    elif isinstance(f, PropositionFormula):
        return Atomic((j, f.id))
    elif isinstance(f, NotFormula):
        return NegConstraint(_valuation(f.child,j,genPr,fMap))
    elif isinstance(f, Multiary):
        op = {AndFormula: AndConstraint, OrFormula: OrConstraint}
        return op[f.__class__]([_valuation(c,j,genPr,fMap) for c in f.children])
    elif isinstance(f, ImpliesFormula):
        return ImpliesConstraint(_valuation(f.left,j,genPr,fMap), _valuation(f.right,j,genPr,fMap))
    elif isinstance(f, FinallyFormula):
        f1 = cachedValuation((f.child,f.gtime), fMap, genPr, _valuation(f.child,f.gtime,genPr,fMap))
        return AndConstraint([_intervalConst(j,f.gtime,f.ltime), f1])
    elif isinstance(f, GloballyFormula):
        f1 = cachedValuation((f.child,f.gtime), fMap, genPr, _valuation(f.child,f.gtime,genPr,fMap))
        return ImpliesConstraint(_intervalConst(j,f.gtime,f.ltime), f1)
    elif isinstance(f, UntilFormula):
        f1 = cachedValuation((f.left,f.gtime), fMap, genPr, _valuation(f.left,f.gtime,genPr,fMap))
        f2 = cachedValuation((f.right,f.gtime), fMap, genPr, _valuation(f.right,f.gtime,genPr,fMap))
        return AndConstraint([_intervalConst(j,f.gtime,f.ltime), f1, f2])
    elif isinstance(f, ReleaseFormula):
        f1 = cachedValuation((f.left,f.gtime), fMap, genPr, _valuation(f.left,f.gtime,genPr,fMap))
        f2 = cachedValuation((f.right,f.gtime), fMap, genPr, _valuation(f.right,f.gtime,genPr,fMap))
        return OrConstraint([NegConstraint(_intervalConst(j,f.gtime,f.ltime)), f1, f2])
    else:
        raise "Something wrong"


def cachedValuation(key, fMap, genPr, value):
    if not key in fMap:
        np = ConstantConstraint(next(genPr))
        fMap[key] = (np, value)
    return fMap[key][0]


def valuationSimple(f:Formula, j:Interval):
    if isinstance(f, ConstantFormula):
        return ConstantConstraint(f.getValue())
    elif isinstance(f, PropositionFormula):
        return Atomic((j, f.id))
    elif isinstance(f, NotFormula):
        return NegConstraint(valuation(f.child, j))
    elif isinstance(f, Multiary):
        op = {AndFormula: AndConstraint, OrFormula: OrConstraint}
        return op[f.__class__]([valuation(c, j) for c in f.children])
    elif isinstance(f, ImpliesFormula):
        return ImpliesConstraint(valuation(f.left, j), valuation(f.right, j))
    elif isinstance(f, FinallyFormula):
        return AndConstraint([_intervalConst(j,f.gtime,f.ltime), valuation(f.child, f.gtime)])
    elif isinstance(f, GloballyFormula):
        return ImpliesConstraint(_intervalConst(j,f.gtime,f.ltime), valuation(f.child, f.gtime))
    elif isinstance(f, UntilFormula):
        return AndConstraint([_intervalConst(j,f.gtime,f.ltime), \
                valuation(f.left, f.gtime), valuation(f.right, f.gtime)])
    elif isinstance(f, ReleaseFormula):
        return OrConstraint([NegConstraint(_intervalConst(j,f.gtime,f.ltime)), \
                valuation(f.left, f.gtime), valuation(f.right, f.gtime)])
    else:
        raise "Something wrong"


def _intervalConst(j:Interval, k:Interval, i:Interval):
    return Atomic((j, k, i))


def fullSeparation(f:Formula, pMap):
    assert f in pMap
    if isinstance(f, Atomic):
        return f
    elif isinstance(f, NotFormula):
        return f.__class__(fullSeparation(f.child, pMap))
    elif isinstance(f, Multiary):
        return f.__class__([fullSeparation(c, pMap) for c in f.children])
    elif isinstance(f, ImpliesFormula):
        return f.__class__(fullSeparation(f.left, pMap), fullSeparation(f.right, pMap))
    elif isinstance(f, UnaryTemporalFormula):
        tf = f.__class__(f.ltime, f.gtime, fullSeparation(f.child, pMap))
        return _separateUnary(tf, 0, pMap[f])
    elif isinstance(f, BinaryTemporalFormula):
        tf = f.__class__(f.ltime, f.gtime, fullSeparation(f.left, pMap), fullSeparation(f.right, pMap))
        return _separateBinary(tf, 0, pMap[f])
    else:
        raise "Something wrong"


def _separateUnary(f:UnaryTemporalFormula, index, partition):
    """
    >>> f = GloballyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
    >>> print(_separateUnary(f, 0, [1,2,3]))
    (([]_[1.0,2.0)^[0.0,1) p) /\ ([]_[1.0,2.0)^[1,1] p) /\ ([]_[1.0,2.0)^(1,2) p) /\ ([]_[1.0,2.0)^[2,2] p) /\ ([]_[1.0,2.0)^(2,3) p) /\ ([]_[1.0,2.0)^[3,3] p) /\ ([]_[1.0,2.0)^(3,inf) p))

    >>> g = FinallyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
    >>> print(_separateUnary(g, 0, [1,2,3]))
    ((<>_[1.0,2.0)^[0.0,1) p) \/ (<>_[1.0,2.0)^[1,1] p) \/ (<>_[1.0,2.0)^(1,2) p) \/ (<>_[1.0,2.0)^[2,2] p) \/ (<>_[1.0,2.0)^(2,3) p) \/ (<>_[1.0,2.0)^[3,3] p) \/ (<>_[1.0,2.0)^(3,inf) p))
    """
    assert f.gtime == universeInterval
    ft = f.__class__
    op = {GloballyFormula: AndFormula, FinallyFormula: OrFormula}
    if index >= len(partition):
        return ft(f.ltime, sepEndPart(index,partition), f.child)
    else:
        (p1, p2) = sepMidPart(index,partition)
        return op[ft]([ft(f.ltime, p1, f.child), ft(f.ltime, p2, f.child), \
                _separateUnary(f, index + 1, partition)])


def _separateBinary(f:BinaryTemporalFormula, index, partition):
    """
    >>> r = UntilFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
    >>> print(_separateBinary(r, 0, [1,2,3]))
    ((p U_(1.0,2.0]^[0.0,1) q) \/ (([]_[0,inf)^[0.0,1) p) /\ ([]_[0,inf)^[1,1] p) /\ ((<>_(1.0,2.0]^[1,1] q) \/ (p U_(1.0,2.0]^(1,2) q) \/ (([]_[0,inf)^(1,2) p) /\ ([]_[0,inf)^[2,2] p) /\ ((<>_(1.0,2.0]^[2,2] q) \/ (p U_(1.0,2.0]^(2,3) q) \/ (([]_[0,inf)^(2,3) p) /\ ([]_[0,inf)^[3,3] p) /\ ((<>_(1.0,2.0]^[3,3] q) \/ (p U_(1.0,2.0]^(3,inf) q))))))))

    >>> s = ReleaseFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
    >>> print(_separateBinary(s, 0, [1,2,3]))
    ((p R_(1.0,2.0]^[0.0,1) q) /\ ((<>_[0,inf)^[0.0,1) p) \/ (<>_[0,inf)^[1,1] p) \/ (([]_(1.0,2.0]^[1,1] q) /\ (p R_(1.0,2.0]^(1,2) q) /\ ((<>_[0,inf)^(1,2) p) \/ (<>_[0,inf)^[2,2] p) \/ (([]_(1.0,2.0]^[2,2] q) /\ (p R_(1.0,2.0]^(2,3) q) /\ ((<>_[0,inf)^(2,3) p) \/ (<>_[0,inf)^[3,3] p) \/ (([]_(1.0,2.0]^[3,3] q) /\ (p R_(1.0,2.0]^(3,inf) q))))))))
    """
    assert f.gtime == universeInterval
    ft  = f.__class__
    op1 = {UntilFormula: OrFormula,       ReleaseFormula: AndFormula}
    op2 = {UntilFormula: AndFormula,      ReleaseFormula: OrFormula}
    st1 = {UntilFormula: GloballyFormula, ReleaseFormula: FinallyFormula}
    st2 = {UntilFormula: FinallyFormula,  ReleaseFormula: GloballyFormula}

    if index >= len(partition):
        return ft(f.ltime, sepEndPart(index, partition), f.left, f.right)
    else:
        (p1, p2) = sepMidPart(index,partition)
        return op1[ft]([ft(f.ltime, p1, f.left, f.right), \
                op2[ft]([
                    st1[ft](universeInterval,p1,f.left), 
                    st1[ft](universeInterval,p2,f.left), \
                    op1[ft]([st2[ft](f.ltime,p2,f.right), \
                            _separateBinary(f, index + 1, partition)])])])

def sepEndPart(index, partition):
    if index == 0:
        return universeInterval
    else:
        return Interval(False, partition[index-1], False, float('inf'))


def sepMidPart(index, partition):
    p2 = Interval(True, partition[index], True, partition[index])
    if index == 0:
        return (Interval(True, 0.0, False, partition[index]), p2)
    else:
        return (Interval(False, partition[index-1], False, partition[index]), p2)

