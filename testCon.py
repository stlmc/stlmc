import sys, gc, time
import base

from stl import *
from concrete import *
from separation import *
from randomSTL import *

from testcase2 import testcase

sys.setrecursionlimit(30000)

def runTest(formula, k):
    baseP = randomBase(k)
    (partition,sepMap) = buildPartition(formula, baseP)
    fs = fullSeparation(formula, sepMap)
    fsize = base.size(fs[0]) + sum([base.size(c) for c in fs[1].values()])
    baseV = randomProp(partition)
    result = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseP, baseV)
    return (result, fsize)


def testGen():
    error = 0
    for fs in range(2,11):
        c = 0
        while c < 100:
            formula = randFormula(fs,5)
            try:
                (result,size) = runTest(formula, 1000)
            except RecursionError:
                error += 1
                if error > 10:
                    print ("Abort")
                    sys.exit(1)
            else:
                print("generating %s @ %s" % (fs,c), file=sys.stderr)
                c += 1
                print('"%s",' % formula)


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
            try:
                stime = time.process_time()
                (result,size) = runTest(formula, k)
                etime = time.process_time() 
            except RecursionError:
                print(",".join(["f%s"%i, str(k), "--"]))
            else:
                print(",".join(["f%s"%i, str(k), str(size), str(result), str(etime-stime)]))
            gc.enable()
            gc.collect()
