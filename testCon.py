import sys, gc, time
import base

from stl import *
from concrete import *
from separation import *
from randomSTL import *

from conInput import testcase

sys.setrecursionlimit(20000)

def runTest(formula, k):
    baseP = randomBase(k)
    partition = buildPartition(formula, baseP)
    fs = fullSeparation(formula, partition[1])
    fsize = base.size(fs[0]) + sum([base.size(c) for c in fs[1].values()])
    baseV = randomProp(partition[0])
    result = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseP, baseV)
    return (result, fsize)


if __name__ == '__main__':
    print("id#size#height#formula")
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        print("#".join(["f%s"%i, str(base.size(formula)), str(formula.height()), testcase[i]]))

    print()
    print("id,k,Separation,Result,Time")
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])

        for k in range(100,1001,100):
            gc.disable()
            stime = time.process_time()
            (result,size) = runTest(formula, k)
            etime = time.process_time() 
            gc.enable()
            gc.collect()
            print(",".join(["f%s"%i, str(k), str(size), str(result), str(etime-stime)]))

