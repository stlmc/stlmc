import gc, time, multiprocessing
import base

import os, sys

from stl import *
from partition import *
from separation import *
from encoding import *

from testcaseSym import testcase
from oneThermostat import Thermostat

sys.setrecursionlimit(30000)

def baseCaseI(baseSize):
    genVar = genId(0, "tau_")
    return [Real(next(genVar)) for _ in range(baseSize)]

def runTest(formula, k):
    baseP = baseCase(k)
    (partition,sepMap,const) = guessPartition(formula, baseP)
    fs = fullSeparation(formula, sepMap)
    baseV = baseEncoding(partition,baseP)
    result = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseV)

    dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
    dRealname = dRealname[:-3]
    dRealname += '_' + str(k) + '.smt2'
    z3constTemp = Thermostat().reach(baseCaseI(k), dRealname)
    z3const = []
    for i in range(len(z3constTemp)):
        z3const.append(z3constTemp[i].z3Obj())
    const.extend(z3const) # thermostat model

    f = open(dRealname, 'a+')
    for i in range(len(z3constTemp)):
        f.write("(assert " + repr(z3constTemp[i]) + ")\n")
    f.write("\n(check-sat)\n(exit)")
 
    z3fs = []
    for i in range(len(fs)):
        z3fs.append(fs[i].z3Obj())

    return (result, const)

def reportTest(formula, filename):
    with open(filename, 'a+') as fle:
        print("id,k,Separation,Result,Generation,Solving", file=fle)
    for k in range(2, 8,2):
        with open(filename, 'a+') as fle:
            stime1 = time.process_time()
            (fullSep,const) = runTest(formula, k)
            etime1 = time.process_time()
            s = z3.Solver()
            s.add(const)
#            s.add(fullSep)
#            f = open("test.smt2", 'w')
#            f.write(s.to_smt2())
            stime2 = time.process_time()
            #s.set("timeout", 1000)
            checkResult = s.check()
            etime2 = time.process_time()
#            print(",".join(["f%s"%i, str(k), str(sizeAst(z3.And(const))+sizeAst(fullSep)), str(checkResult), str(etime1-stime1),str(etime2-stime2)]), file=fle)
#            print(s.to_smt2())
#            print (s.model())


if __name__ == '__main__':
    print("id#size#height#formula")
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        print("#".join(["f%s"%i, str(base.size(formula)), str(formula.height()), testcase[i]]))

    print()
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        print ("scheduleing f%s: "%i + str(formula))
        p = multiprocessing.Process(target = reportTest, args=(formula, "output-f%s"%i))
        p.start()
    
