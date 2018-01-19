"""
>>> f = GloballyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
>>> print(_separateUnary(f, 0, [1,2,3]))
((([]_[1.0,2.0)^[0.0,1) p) /\ ([]_[1.0,2.0)^[1,1] p)) /\ ((([]_[1.0,2.0)^(1,2) p) /\ ([]_[1.0,2.0)^[2,2] p)) /\ ((([]_[1.0,2.0)^(2,3) p) /\ ([]_[1.0,2.0)^[3,3] p)) /\ ([]_[1.0,2.0)^(3,inf) p))))

>>> g = FinallyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
>>> print(_separateUnary(g, 0, [1,2,3]))
(((<>_[1.0,2.0)^[0.0,1) p) \/ (<>_[1.0,2.0)^[1,1] p)) \/ (((<>_[1.0,2.0)^(1,2) p) \/ (<>_[1.0,2.0)^[2,2] p)) \/ (((<>_[1.0,2.0)^(2,3) p) \/ (<>_[1.0,2.0)^[3,3] p)) \/ (<>_[1.0,2.0)^(3,inf) p))))

>>> r = UntilFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
>>> print(_separateBinary(r, 0, ['v1','v2']))
((p U_(1.0,2.0]^[0.0,'v1') q) \/ ((([]_[0,inf)^[0.0,'v1') p) /\ ([]_[0,inf)^['v1','v1'] p)) /\ ((<>_(1.0,2.0]^['v1','v1'] q) \/ ((p U_(1.0,2.0]^('v1','v2') q) \/ ((([]_[0,inf)^('v1','v2') p) /\ ([]_[0,inf)^['v2','v2'] p)) /\ ((<>_(1.0,2.0]^['v2','v2'] q) \/ (p U_(1.0,2.0]^('v2',inf) q)))))))

>>> s = ReleaseFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
>>> print(_separateBinary(s, 0, ['v1','v2']))
((p R_(1.0,2.0]^[0.0,'v1') q) /\ (((<>_[0,inf)^[0.0,'v1') p) \/ (<>_[0,inf)^['v1','v1'] p)) \/ (([]_(1.0,2.0]^['v1','v1'] q) /\ ((p R_(1.0,2.0]^('v1','v2') q) /\ (((<>_[0,inf)^('v1','v2') p) \/ (<>_[0,inf)^['v2','v2'] p)) \/ (([]_(1.0,2.0]^['v2','v2'] q) /\ (p R_(1.0,2.0]^('v2',inf) q)))))))
"""

from formula import *
from interval import *
from expr import *


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


