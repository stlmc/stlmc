
import random
from formula import *

def randomBase(size:int):
    base = [0]
    for _ in range(size):
        base.append(base[-1] + random.random()*10)
    return base


def randomProp(partition:dict):
    bmap = {}
    for (f,par) in partition.items():
        if isinstance(f, PropositionFormula):
            bmap[f] = [bool(random.getrandbits(1)) for _ in range(len(par))]
    return bmap

def randFormula(fsize:int, vsize:int):
    gen = genId(1, "p")
    atoms = [ConstantFormula(True), ConstantFormula(False)]
    atoms.extend([PropositionFormula(next(gen)) for _ in range(vsize)])
    return _randFormula(fsize, atoms)

def _randInterval():
    lend = True if random.getrandbits(1) else False
    rend = True if random.getrandbits(1) else False
    lval = random.uniform(0,5)
    rval = lval + random.uniform(0,5)
    return Interval(lend,lval,rend,rval)

def _randFormula(fs:int, atoms):
    if fs <= 0:
        return random.choice(atoms)
    elif fs == 1:
        return _randUnaryFormula(fs, atoms)
    else:
        if random.getrandbits(1):
            return _randUnaryFormula(fs, atoms)
        else:
            return _randBinaryFormula(fs, atoms)


def _randUnaryFormula(fs:int, atoms):
    if random.randrange(3) > 0:
        op = random.choice([GloballyFormula,FinallyFormula])
        return op( _randInterval(), universeInterval, _randFormula(fs-1, atoms))
    else:
        return NotFormula(_randFormula(fs-1, atoms))


def _randBinaryFormula(fs:int, atoms):
    lsize = random.randrange(fs-1)
    left  = _randFormula(lsize, atoms)
    right = _randFormula(fs-lsize-1, atoms)

    c = random.randrange(5)
    if c > 2:
        op = random.choice([UntilFormula,ReleaseFormula])
        return op(_randInterval(), universeInterval, left, right)
    elif c == 2: 
        return ImpliesFormula(left, right)
    else:
        op = random.choice([AndFormula,OrFormula])
        return op([left, right])

