import sys, gc, time
import base

from stl import *
from concrete import *
from separation import *
from randomProp import *

sys.setrecursionlimit(10000)

testcase = [
    "[] (0,1) p",
    "p U [0,4) q",
    "(<> [1,2] p) U (0.5,3) p",
    "[] [0,1] (p -> <> [1,2] q)",
    "[] [0,1] (p -> q U [1,2] r)",
    "<> (0,0.4) ([] [0,1] (p -> q U [1,2] r))",
    "[] [0,1] (p -> <> [1,2] (q /\ [] [3,3] r))",
    "[] [0,1] (p -> (~r U [1,2] (q /\ [] [3,4] r)))",
    "(<> (1,2) r) U [0,1] (p -> (~s U [1,2] (q /\ [] [3,4] r)))",
    "([] (1,2) <> (1,2) ~r) U [0,1] (~p -> (s U [1,2] (q /\ [] [3,4] r)))"
]

def runTest(formula, k):
    baseP = randomBase(k)
    partition = buildPartition(formula, baseP)
    fs = fullSeparation(formula, partition[1])
    fsize = base.size(fs[0]) + sum([base.size(c) for c in fs[1].values()])
    baseV = randomProp(partition[0])
    result = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseP, baseV)
    return (result, fsize)


if __name__ == '__main__':
    for f in testcase:
        formula = parseFormula(f)
        print("Checking: " + str(formula))

        print("size: %s, height: %s" % (base.size(formula), formula.height()))

        print("k,Separation,Result,Time")
        for k in range(100,1001,100):
            gc.disable()
            stime = time.process_time()
            (result,size) = runTest(formula, k)
            etime = time.process_time() 
            gc.enable()
            gc.collect()
            print(",".join([str(k), str(size), str(result), str(etime-stime)]))

