from .constraints import *
from functools import singledispatch

from .operations import generate_id


def fullSeparation(f: Formula, sepMap):
    fMap = {}
    gen = generate_id(0, "@chi")
    return (_separation(f, sepMap, gen, fMap), fMap)


@singledispatch
def _separation(f: Formula, sepMap, gen, fMap):
    raise NotImplementedError('Something wrong')


@_separation.register(Constant)
def _(f: Formula, sepMap, gen, fMap):
    return f


@_separation.register(Bool)
def _(f: Formula, sepMap, gen, fMap):
    return f


@_separation.register(Not)
def _(f: Not, sepMap, gen, fMap):
    return f.__class__(_separation(f.child, sepMap, gen, fMap))


@_separation.register(Multinary)
def _(f: Multinary, sepMap, gen, fMap):
    return f.__class__([_separation(c, sepMap, gen, fMap) for c in f.children])


@_separation.register(Implies)
def _(f: Implies, sepMap, gen, fMap):
    return f.__class__(_separation(f.left, sepMap, gen, fMap), _separation(f.right, sepMap, gen, fMap))


@_separation.register(UnaryTemporalFormula)
def _(f: UnaryTemporalFormula, sepMap, gen, fMap):
    np = Bool(next(gen))
    fMap[(np, f.local_time)] = _separation(f.child, sepMap, gen, fMap)
    tf = f.__class__(f.local_time, f.global_time, np)
    return _separateUnary(tf, 0, sepMap[f])


@_separation.register(BinaryTemporalFormula)
def _(f: BinaryTemporalFormula, sepMap, gen, fMap):
    np1 = Bool(next(gen))
    np2 = Bool(next(gen))
    fMap[(np1, f.local_time)] = _separation(f.left, sepMap, gen, fMap)
    fMap[(np2, f.local_time)] = _separation(f.right, sepMap, gen, fMap)
    tf = f.__class__(f.local_time, f.global_time, np1, np2)
    return _separateBinary(tf, 0, sepMap[f])


def _separateUnary(f: UnaryTemporalFormula, index, partition):
    """
    >>> f = GloballyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
    >>> print(_separateUnary(f, 0, [1,2,3]))
    (([]_[1.0,2.0)^[0.0,1) p) /\ ([]_[1.0,2.0)^[1,1] p) /\ ([]_[1.0,2.0)^(1,2) p) /\ ([]_[1.0,2.0)^[2,2] p) /\ ([]_[1.0,2.0)^(2,3) p) /\ ([]_[1.0,2.0)^[3,3] p) /\ ([]_[1.0,2.0)^(3,inf) p))

    >>> g = FinallyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
    >>> print(_separateUnary(g, 0, [1,2,3]))
    ((<>_[1.0,2.0)^[0.0,1) p) \/ (<>_[1.0,2.0)^[1,1] p) \/ (<>_[1.0,2.0)^(1,2) p) \/ (<>_[1.0,2.0)^[2,2] p) \/ (<>_[1.0,2.0)^(2,3) p) \/ (<>_[1.0,2.0)^[3,3] p) \/ (<>_[1.0,2.0)^(3,inf) p))
    """
    assert f.global_time == universeInterval
    ft = f.__class__
    op = {GloballyFormula: And, FinallyFormula: Or}
    if index >= len(partition):
        return ft(f.local_time, _sepEndPart(index, partition), f.child)
    else:
        (p1, p2) = _sepMidPart(index, partition)
        return op[ft]([ft(f.local_time, p1, f.child), ft(f.local_time, p2, f.child),
                       _separateUnary(f, index + 1, partition)])


def _separateBinary(f: BinaryTemporalFormula, index, partition):
    """
    >>> r = UntilFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
    >>> print(_separateBinary(r, 0, [1,2,3]))
    ((p U_(1.0,2.0]^[0.0,1) q) \/ (([]_[0,inf)^[0.0,1) p) /\ ([]_[0,inf)^[1,1] p) /\ ((<>_(1.0,2.0]^[1,1] q) \/ (p U_(1.0,2.0]^(1,2) q) \/ (([]_[0,inf)^(1,2) p) /\ ([]_[0,inf)^[2,2] p) /\ ((<>_(1.0,2.0]^[2,2] q) \/ (p U_(1.0,2.0]^(2,3) q) \/ (([]_[0,inf)^(2,3) p) /\ ([]_[0,inf)^[3,3] p) /\ ((<>_(1.0,2.0]^[3,3] q) \/ (p U_(1.0,2.0]^(3,inf) q))))))))

    >>> s = ReleaseFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
    >>> print(_separateBinary(s, 0, [1,2,3]))
    ((p R_(1.0,2.0]^[0.0,1) q) /\ ((<>_[0,inf)^[0.0,1) p) \/ (<>_[0,inf)^[1,1] p) \/ (([]_(1.0,2.0]^[1,1] q) /\ (p R_(1.0,2.0]^(1,2) q) /\ ((<>_[0,inf)^(1,2) p) \/ (<>_[0,inf)^[2,2] p) \/ (([]_(1.0,2.0]^[2,2] q) /\ (p R_(1.0,2.0]^(2,3) q) /\ ((<>_[0,inf)^(2,3) p) \/ (<>_[0,inf)^[3,3] p) \/ (([]_(1.0,2.0]^[3,3] q) /\ (p R_(1.0,2.0]^(3,inf) q))))))))
    """
    assert f.global_time == universeInterval
    ft = f.__class__
    op1 = {UntilFormula: Or, ReleaseFormula: And}
    op2 = {UntilFormula: And, ReleaseFormula: Or}
    st1 = {UntilFormula: GloballyFormula, ReleaseFormula: FinallyFormula}
    st2 = {UntilFormula: FinallyFormula, ReleaseFormula: GloballyFormula}

    if index >= len(partition):
        return ft(f.local_time, _sepEndPart(index, partition), f.left, f.right)
    else:
        (p1, p2) = _sepMidPart(index, partition)
        return op1[ft]([ft(f.local_time, p1, f.left, f.right),
                        op2[ft]([
                            st1[ft](universeInterval, p1, f.left),
                            st1[ft](universeInterval, p2, f.left),
                            op1[ft]([st2[ft](f.local_time, p2, f.right),
                                     _separateBinary(f, index + 1, partition)])])])


def _sepEndPart(index, partition):
    if index == 0:
        return universeInterval
    else:
        return Interval(False, partition[index - 1], False, float('inf'))


def _sepMidPart(index, partition):
    p2 = Interval(True, partition[index], True, partition[index])
    if index == 0:
        return Interval(True, 0.0, False, partition[index]), p2
    else:
        return Interval(False, partition[index - 1], False, partition[index]), p2
