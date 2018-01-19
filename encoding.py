
from formula import *
from interval import *
from expr import *


def valuation(f:Formula, j:Interval):
    if isinstance(f, ConstantFormula):
        return ConstantConstraint(f.getValue())
    elif isinstance(f, PropositionFormula):
        return Atomic((j, f.id))
    elif isinstance(f, NotFormula):
        return NegConstraint(valuation(f.child, j))
    elif isinstance(f, BinaryFormula):
        op = {AndFormula: AndConstraint, OrFormula: OrConstraint, ImpliesFormula: ImpliesConstraint}
        return op[f.__class__](valuation(f.left, j), valuation(f.right, j))
    elif isinstance(f, UnaryTemporalFormula):
        op = {GloballyFormula: ImpliesConstraint, FinallyFormula: AndConstraint}
        return op[f.__class__](_intervalConst(j,f.gtime,f.ltime), valuation(f.child, f.gtime))
    elif isinstance(f, BinaryTemporalFormula):
        top = {ReleaseFormula: ImpliesConstraint, UntilFormula: AndConstraint}
        bop = {ReleaseFormula: OrConstraint,      UntilFormula: AndConstraint}
        return top[f.__class__](_intervalConst(j,f.gtime,f.ltime), \
                bop[f.__class__](valuation(f.left, f.gtime), valuation(f.right, f.gtime)))
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
    elif isinstance(f, BinaryFormula):
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
    ((([]_[1.0,2.0)^[0.0,1) p) /\ ([]_[1.0,2.0)^[1,1] p)) /\ ((([]_[1.0,2.0)^(1,2) p) /\ ([]_[1.0,2.0)^[2,2] p)) /\ ((([]_[1.0,2.0)^(2,3) p) /\ ([]_[1.0,2.0)^[3,3] p)) /\ ([]_[1.0,2.0)^(3,inf) p))))

    >>> g = FinallyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
    >>> print(_separateUnary(g, 0, [1,2,3]))
    (((<>_[1.0,2.0)^[0.0,1) p) \/ (<>_[1.0,2.0)^[1,1] p)) \/ (((<>_[1.0,2.0)^(1,2) p) \/ (<>_[1.0,2.0)^[2,2] p)) \/ (((<>_[1.0,2.0)^(2,3) p) \/ (<>_[1.0,2.0)^[3,3] p)) \/ (<>_[1.0,2.0)^(3,inf) p))))
    """
    assert f.gtime == universeInterval
    ft = f.__class__
    op = {GloballyFormula: AndFormula, FinallyFormula: OrFormula}
    if index >= len(partition):
        p1 = universeInterval if index == 0 else Interval(False, partition[index-1], False, float('inf'))
        return ft(f.ltime, p1, f.child)
    else:
        p1 = Interval(True, 0.0, False, partition[index]) if index == 0 else \
                Interval(False, partition[index-1], False, partition[index])
        p2 = Interval(True, partition[index], True, partition[index])
        return op[ft](op[ft](ft(f.ltime, p1, f.child), ft(f.ltime, p2, f.child)), \
                _separateUnary(f, index + 1, partition))


def _separateBinary(f:BinaryTemporalFormula, index, partition):
    """
    >>> r = UntilFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
    >>> print(_separateBinary(r, 0, [1,2]))
    ((p U_(1.0,2.0]^[0.0,1) q) \/ ((([]_[0,inf)^[0.0,1) p) /\ ([]_[0,inf)^[1,1] p)) /\ ((<>_(1.0,2.0]^[1,1] q) \/ ((p U_(1.0,2.0]^(1,2) q) \/ ((([]_[0,inf)^(1,2) p) /\ ([]_[0,inf)^[2,2] p)) /\ ((<>_(1.0,2.0]^[2,2] q) \/ (p U_(1.0,2.0]^(2,inf) q)))))))

    >>> s = ReleaseFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
    >>> print(_separateBinary(s, 0, [1,2]))
    ((p R_(1.0,2.0]^[0.0,1) q) /\ (((<>_[0,inf)^[0.0,1) p) \/ (<>_[0,inf)^[1,1] p)) \/ (([]_(1.0,2.0]^[1,1] q) /\ ((p R_(1.0,2.0]^(1,2) q) /\ (((<>_[0,inf)^(1,2) p) \/ (<>_[0,inf)^[2,2] p)) \/ (([]_(1.0,2.0]^[2,2] q) /\ (p R_(1.0,2.0]^(2,inf) q)))))))
    """
    assert f.gtime == universeInterval
    ft  = f.__class__
    op1 = {UntilFormula: OrFormula,       ReleaseFormula: AndFormula}
    op2 = {UntilFormula: AndFormula,      ReleaseFormula: OrFormula}
    st1 = {UntilFormula: GloballyFormula, ReleaseFormula: FinallyFormula}
    st2 = {UntilFormula: FinallyFormula,  ReleaseFormula: GloballyFormula}

    if index >= len(partition):
        p1 = universeInterval if index == 0 else Interval(False, partition[index-1], False, float('inf'))
        return ft(f.ltime, p1, f.left, f.right)
    else:
        p1 = Interval(True, 0.0, False, partition[index]) if index == 0 else \
                Interval(False, partition[index-1], False, partition[index])
        p2 = Interval(True, partition[index], True, partition[index])
        return op1[ft](ft(f.ltime, p1, f.left, f.right), \
                op2[ft](
                    op2[ft](st1[ft](universeInterval,p1,f.left), \
                            st1[ft](universeInterval,p2,f.left)), \
                    op1[ft](st2[ft](f.ltime,p2,f.right), \
                            _separateBinary(f, index + 1, partition))))


