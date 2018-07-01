import gc, time, multiprocessing
import base

from stl import *
from partition import *
from separation import *
from encoding import *

from testcaseSym import testcase
from thermoSimple import Thermostat

sys.setrecursionlimit(30000)

def runTest(formula, k):
    baseP = baseCase(k)
    (partition,sepMap,const) = guessPartition(formula, baseP)
    fs = fullSeparation(formula, sepMap)
    baseV = baseEncoding(partition,baseP)
    result = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseV)

    const.extend(Thermostat().reach(baseP)) # thermostat model
     
    return (result, const)

def reportTest(formula, filename):
    with open(filename, 'a+') as fle:
        print("id,k,Separation,Result,Generation,Solving", file=fle)
    for k in range(2,101,2):
        with open(filename, 'a+') as fle:
            stime1 = time.process_time()
            (fullSep,const) = runTest(formula, k)
            etime1 = time.process_time()
            s = Solver()
            for i in range(len(const)):
                s.add(const[i].z3Obj())
            s.add(fullSep)
            stime2 = time.process_time()
            #s.set("timeout", 1000)
            checkResult = s.check()
            etime2 = time.process_time()
            print(",".join(["f%s"%i, str(k), str(sizeAst(And(const))+sizeAst(fullSep)), str(checkResult), str(etime1-stime1),str(etime2-stime2)]), file=fle)
            print(s.to_smt2())
            print (s.model())


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
    
