import gc, time, multiprocessing
import core.base

import os, sys

from core.stl import *
from core.partition import *
from core.separation import *
from core.encoding import *

from testcaseSym import testcase
from oneThermostat import Thermostat

sys.setrecursionlimit(30000)

def runTest(formula, k):
    baseP = baseCase(k)
    (partition,sepMap,const) = guessPartition(formula, baseP)
    fs = fullSeparation(formula, sepMap)
    baseV = baseEncoding(partition,baseP)
    result = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseV)

    z3const = []
    for i in range(len(const)):
        z3const.append(const[i].z3Obj())

    dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
    dRealname = dRealname[:-3]
    dRealname += '_' + str(k) + '.smt2'
    (constTemp, printObject) = Thermostat().reach(baseCase(k), dRealname)
    
    for i in range(len(constTemp)):
        z3const.append(constTemp[i].z3Obj())

    printObject.addConst([result])
    printObject.addConst(const)
    printObject.callAll()
    
    return (result.z3Obj(), z3const)

def reportTest(formula):
    for k in range(5,6,2):
        (fullSep,const) = runTest(formula, k)
        s = z3.Solver()
        s.add(const)
        s.add(fullSep)
        print(s.to_smt2())
        s.set("timeout", 5000)
        checkResult = s.check()
        print(checkResult)
#         print(",".join(["f%s"%i, str(k), str(sizeAst(z3.And(const))+sizeAst(fullSep)), str(checkResult), str(etime1-stime1),str(etime2-stime2)]), file=fle)
#        print(s.to_smt2())
#        print (s.model())


if __name__ == '__main__':
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        reportTest(formula)
    
