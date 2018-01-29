
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
            bmap[f] = [bool(random.getrandbits(1)) for _ in range(len(par)+1)]
    return bmap
