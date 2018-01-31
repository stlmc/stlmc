import gc, time
import base

from stl import *
from partition import *
from separation import *
from encoding import *

from testcaseSym import testcase
from model import Thermostat


def runTest(formula, k):
    baseP = baseCase(k)
    (partition,sepMap,const) = guessPartition(formula, baseP)
    fs = fullSeparation(formula, sepMap)
    baseV = baseEncoding(partition,baseP)
    result = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseV)

    const.extend(Thermostat().reach(baseP)) # thermostat model
    return (result, const)


if __name__ == '__main__':
    print("id#size#height#formula")
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        print("#".join(["f%s"%i, str(base.size(formula)), str(formula.height()), testcase[i]]))

    print()
    print("id,k,Separation,Result,Generation,Solving")
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])

        for k in range(2,21,2):
            stime1 = time.process_time()
            (fullSep,const) = runTest(formula, k)
            etime1 = time.process_time()
            s = Solver()
            s.add(const)
            s.add(fullSep)
            stime2 = time.process_time()
            #s.set("timeout", 1000)
            checkResult = s.check()
            etime2 = time.process_time()
            print(",".join(["f%s"%i, str(k), str(sizeAst(And(const))+sizeAst(fullSep)), str(checkResult), str(etime1-stime1),str(etime2-stime2)]))
            #print(s.to_smt2())
            #print (s.model())

