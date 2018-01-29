import sys
import time

from stl import *
from concrete import *
from separation import *
from randomProp import *

sys.setrecursionlimit(5000)

testcase = [
    "[] (0,1) p",
    "p U [0,4) q",
    "[] [0,1] (p -> <> [1,2] q)",
    "[] [0,1] (p -> q U [1,2] r)",
    "(<> (1,3] s) R [0,1] (p -> q U [1,2] r)",
    "[] [0,1] (p -> <> [1,2] (q /\ [] [3,4] r))",
    "[] [0,1] (p -> (~r U [1,2] (q /\ [] [3,4] r)))",
    "(<> (1,2) ~r) U [0,1] (p -> (s U [1,2] (q /\ [] [3,4] r)))"
]

def runTest(formula, k):
    baseP = randomBase(k)
    partition = buildPartition(formula, baseP)
    fs = fullSeparation(formula, partition)
    baseV = randomProp(partition)
    result = valuation(fs, Interval(True, 0.0, True, 0.0), baseP, baseV)
    return (result, fs.size())


if __name__ == '__main__':
    for f in testcase:
        formula = parseFormula(f)
        print("Checking: " + str(formula))
        
        for k in range(1,20):
            print("k = " + str(k)) 
            
            stime = time.time()
            (result,size) = runTest(formula, k)
            etime = time.time() 
            
            print("    Separation: " + str(size)) 
            print("    Result: " + str(result)) 
            print("    Time: " + str(etime-stime))

