from .constraints import *
from functools import singledispatch

from .operations import generate_id
import re


def fullSeparation(f: Formula, sepMap):
    fMap = {}
    gen = generate_id(0, "@chi")
    return (_separation(f, sepMap, gen, fMap), fMap)


@singledispatch
def _separation(f: Formula, sepMap, gen, fMap):
    raise NotImplementedError('Something wrong')


@_separation.register(Constant)
def _(f: Constant, sepMap, gen, fMap):
    return f


@_separation.register(Bool)
def _(f: Bool, sepMap, gen, fMap):
    return f


@_separation.register(Not)
def _(f: Not, sepMap, gen, fMap):
    if isinstance(f.child, Bool):
        return Bool("not@" + f.child.id)
    return f.__class__(_separation(f.child, sepMap, gen, fMap))


@_separation.register(Multinary)
def _(f: Multinary, sepMap, gen, fMap):
    flatten = list()
    ft = f.__class__
    result = [_separation(c, sepMap, gen, fMap) for c in f.children]
    for r in result:
        if isinstance(r, ft):
            flatten.extend(r.children)
        else:
            flatten.append(r)
    return f.__class__(flatten)


@_separation.register(Implies)
def _(f: Implies, sepMap, gen, fMap):
    return f.__class__(_separation(f.left, sepMap, gen, fMap), _separation(f.right, sepMap, gen, fMap))


@_separation.register(UnaryTemporalFormula)
def _(f: UnaryTemporalFormula, sepMap, gen, fMap):
    np = Bool(next(gen))
    fMap[(np, f.local_time)] = _separation(f.child, sepMap, gen, fMap)
    tf = f.__class__(f.local_time, f.global_time, np)
    ft = tf.__class__
    op = {GloballyFormula: And, FinallyFormula: Or}
    global_time = f.global_time
    sep_point = list(sepMap[f])
    sep_point = sorted(sep_point, key=lambda x: int(re.findall("\d+", x.id)[0]))
    if isinstance(global_time.left, float):
        left = RealVal(str(global_time.left))
    else:
        left = global_time.left
    sep_point = [left] + sep_point
    if isinstance(global_time.right, float):
        right = RealVal(str(global_time.right))
    else:
        right = global_time.right
    sep_point = sep_point + [right]

    result = _separateUnary(tf, 0, sep_point)

    return op[ft](result)


@_separation.register(BinaryTemporalFormula)
def _(f: BinaryTemporalFormula, sepMap, gen, fMap):
    np1 = Bool(next(gen))
    np2 = Bool(next(gen))
    fMap[(np1, f.local_time)] = _separation(f.left, sepMap, gen, fMap)
    fMap[(np2, f.local_time)] = _separation(f.right, sepMap, gen, fMap)
    tf = f.__class__(f.local_time, f.global_time, np1, np2)
    op1 = {UntilFormula: Or, ReleaseFormula: And}
    global_time = f.global_time
    sep_point = list(sepMap[f])
    sep_point = sorted(sep_point, key=lambda x: int(re.findall("\d+", x.id)[0]))
    if isinstance(global_time.left, float):
        left = RealVal(str(global_time.left))
    else:
        left = global_time.left
    sep_point = [left] + sep_point
    if isinstance(global_time.right, float):
        right = RealVal(str(global_time.right))
    else:
        right = global_time.right
    sep_point = sep_point + [right]
    result = _separateBinary(tf, 0, sep_point)

    return result


def _separateUnary(f: UnaryTemporalFormula, index, partition):
    """
    >>> f = GloballyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
    >>> print(_separateUnary(f, 0, [1,2,3]))
    (([]_[1.0,2.0)^[0.0,1) p) /\ ([]_[1.0,2.0)^[1,1] p) /\ ([]_[1.0,2.0)^(1,2) p) /\ ([]_[1.0,2.0)^[2,2] p) /\ ([]_[1.0,2.0)^(2,3) p) /\ ([]_[1.0,2.0)^[3,3] p) /\ ([]_[1.0,2.0)^(3,inf) p))

    >>> g = FinallyFormula(Interval(True, 1.0, False, 2.0), universeInterval, PropositionFormula('p'))
    >>> print(_separateUnary(g, 0, [1,2,3]))
    ((<>_[1.0,2.0)^[0.0,1) p) \/ (<>_[1.0,2.0)^[1,1] p) \/ (<>_[1.0,2.0)^(1,2) p) \/ (<>_[1.0,2.0)^[2,2] p) \/ (<>_[1.0,2.0)^(2,3) p) \/ (<>_[1.0,2.0)^[3,3] p) \/ (<>_[1.0,2.0)^(3,inf) p))
    """
    # assert f.global_time == universeInterval
    ft = f.__class__
    result = list()
    op = {GloballyFormula: And, FinallyFormula: Or}
    if index >= len(partition) - 1:
        return list()
    else:
        (p1, p2) = _sepMidPart(index, partition)
        result.extend([ft(f.local_time, p1, f.child), ft(f.local_time, p2, f.child)])
        result.extend(_separateUnary(f, index + 1, partition))
        return result


def _separateBinary(f: BinaryTemporalFormula, index, partition):
    """
    >>> r = UntilFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
    >>> print(_separateBinary(r, 0, [1,2,3]))
    ((p U_(1.0,2.0]^[0.0,1) q) \/ (([]_[0,inf)^[0.0,1) p) /\ ([]_[0,inf)^[1,1] p) /\ ((<>_(1.0,2.0]^[1,1] q) \/ (p U_(1.0,2.0]^(1,2) q) \/ (([]_[0,inf)^(1,2) p) /\ ([]_[0,inf)^[2,2] p) /\ ((<>_(1.0,2.0]^[2,2] q) \/ (p U_(1.0,2.0]^(2,3) q) \/ (([]_[0,inf)^(2,3) p) /\ ([]_[0,inf)^[3,3] p) /\ ((<>_(1.0,2.0]^[3,3] q) \/ (p U_(1.0,2.0]^(3,inf) q))))))))

    >>> s = ReleaseFormula(Interval(False, 1.0, True, 2.0), universeInterval, PropositionFormula('p'), PropositionFormula('q'))
    >>> print(_separateBinary(s, 0, [1,2,3]))
    ((p R_(1.0,2.0]^[0.0,1) q) /\ ((<>_[0,inf)^[0.0,1) p) \/ (<>_[0,inf)^[1,1] p) \/ (([]_(1.0,2.0]^[1,1] q) /\ (p R_(1.0,2.0]^(1,2) q) /\ ((<>_[0,inf)^(1,2) p) \/ (<>_[0,inf)^[2,2] p) \/ (([]_(1.0,2.0]^[2,2] q) /\ (p R_(1.0,2.0]^(2,3) q) /\ ((<>_[0,inf)^(2,3) p) \/ (<>_[0,inf)^[3,3] p) \/ (([]_(1.0,2.0]^[3,3] q) /\ (p R_(1.0,2.0]^(3,inf) q))))))))
    """
    # assert f.global_time == universeInterval
    ft = f.__class__
    op1 = {UntilFormula: Or, ReleaseFormula: And}
    op2 = {UntilFormula: And, ReleaseFormula: Or}
    st1 = {UntilFormula: GloballyFormula, ReleaseFormula: FinallyFormula}
    st2 = {UntilFormula: FinallyFormula, ReleaseFormula: GloballyFormula}
    result = list()
    if index == 0:
        (p1, p2) = _sepMidPart(index, partition)
        sub_part = st1[ft](Interval(True, RealVal("0"), False, RealVal('inf')), p1, f.left)
        subresult = list()
        subresult.append(st2[ft](f.local_time, p1, f.right))
        subresult.append(_separateBinary(f, index + 1, partition))
        return op2[ft]([sub_part, op1[ft](subresult)])
    elif index >= len(partition) - 1:
        return ft(f.local_time, Interval(False, partition[-2], False, partition[-1]), f.left, f.right)
    else:
        (p1, p2) = _sepMidPart(index - 1, partition)
        result.append(ft(f.local_time, p2, f.left, f.right))
        subresult = list()
        subresult.append(st1[ft](Interval(True, RealVal("0"), False, RealVal('inf')), p2, f.left))
        (p1, p2) = _sepMidPart(index, partition)
        subresult.append(st1[ft](Interval(True, RealVal("0"), False, RealVal('inf')), p1, f.left))
        sub_part = list()
        sub_part.append(st2[ft](f.local_time, p1, f.right))
        sub_part.append(_separateBinary(f, index + 1, partition))
        subresult.append(Or(sub_part))
        result.append(And(subresult))
        return Or(result)


def _sepEndPart(index, partition):
    if index == 0:
        return universeInterval
    else:
        return Interval(False, partition[index - 1], False, RealVal('inf'))


def _sepMidPart(index, partition):
    p2 = Interval(True, partition[index], True, partition[index])
    return p2, Interval(False, partition[index], False, partition[index + 1])
