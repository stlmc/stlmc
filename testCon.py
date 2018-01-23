
import random
from stl import *
from concrete import *
from separation import *


f1 = "[] [0,1] ~p /\ [] =1 q /\ <> (2.1,inf) true \/ (false U [0,4) q)"
f2 = "[] [0,1] (p -> <> [1,2] q)"
f3 = "[] [0,1] (p -> q U [1,2] r)"
f4 = "(<> (1,3] s) R [0,1] (p -> q U [1,2] r)"
f5 = "[] [0,1] (p -> <> [1,2] (q /\ [] [3,4] r))"
f6 = "[] [0,1] (p -> (~r U [1,2] (q /\ [] [3,4] r)))"
f7 = "(<> (1,2) ~r) U [0,1] (p -> (s U [1,2] (q /\ [] [3,4] r)))"

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


if __name__ == '__main__':
    formula = parseFormula(f5)
    print(formula)
    print()

    baseP = randomBase(10)
    partition = buildPartition(formula, randomBase(10))
    #for (k,v) in partition.items():
    #    print(str(k) + ': ' + ', '.join([str(x) for x in v]))

    fs = fullSeparation(formula, partition)
    #print(fs)
    print("Separation: " + str(fs.size()))

    baseV = randomProp(partition)
    result = valuation(fs, Interval(True, 0.0, True, 0.0), baseP, baseV)
    print(result)
