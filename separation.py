
from formula import *
from functools import singledispatch

@singledispatch
def fullSeparation(f:Formula, pMap):
    raise NotImplementedError('Something wrong')

@fullSeparation.register(Atomic)
def _(f:Formula, pMap):
    return f

@fullSeparation.register(NotFormula)
def _(f:Formula, pMap):
    return f.__class__(fullSeparation(f.child, pMap))

@fullSeparation.register(Multiary)
def _(f:Formula, pMap):
    return f.__class__([fullSeparation(c, pMap) for c in f.children])

@fullSeparation.register(ImpliesFormula)
def _(f:Formula, pMap):
    return f.__class__(fullSeparation(f.left, pMap), fullSeparation(f.right, pMap))

@fullSeparation.register(UnaryTemporalFormula)
def _(f:Formula, pMap):
    tf = f.__class__(f.ltime, f.gtime, fullSeparation(f.child, pMap))
    return _separateUnary(tf, 0, pMap[f])

@fullSeparation.register(BinaryTemporalFormula)
def _(f:Formula, pMap):
    tf = f.__class__(f.ltime, f.gtime, fullSeparation(f.left, pMap), fullSeparation(f.right, pMap))
    return _separateBinary(tf, 0, pMap[f])


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
        return ft(f.ltime, _sepEndPart(index,partition), f.child)
    else:
        (p1, p2) = _sepMidPart(index,partition)
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
        return ft(f.ltime, _sepEndPart(index, partition), f.left, f.right)
    else:
        (p1, p2) = _sepMidPart(index,partition)
        return op1[ft]([ft(f.ltime, p1, f.left, f.right), \
                op2[ft]([
                    st1[ft](universeInterval,p1,f.left), 
                    st1[ft](universeInterval,p2,f.left), \
                    op1[ft]([st2[ft](f.ltime,p2,f.right), \
                            _separateBinary(f, index + 1, partition)])])])


def _sepEndPart(index, partition):
    if index == 0:
        return universeInterval
    else:
        return Interval(False, partition[index-1], False, float('inf'))


def _sepMidPart(index, partition):
    p2 = Interval(True, partition[index], True, partition[index])
    if index == 0:
        return (Interval(True, 0.0, False, partition[index]), p2)
    else:
        return (Interval(False, partition[index-1], False, partition[index]), p2)
