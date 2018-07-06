import z3
import os, sys
import gc, time, multiprocessing
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
import core.base
from core.stl import *
from core.dRealHandler import *
from core.z3Handler import *

from testcaseSym import testcase
from oneThermostat import Thermostat

sys.setrecursionlimit(10000)

def runTest(formula, k):

    model = Thermostat()
    const = model.modelCheck(formula, k)
    # z3
    z3const = [z3Obj(i) for i in const]

    # dReal
    dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
    dRealname = dRealname[:-3]
    dRealname += '_' + str(k) + '.smt2'
    
    with open(dRealname, 'w') as fle:
        printObject = dRealHandler(const, fle, model.variables, model.flowDict)
        printObject.addConst(const)
        printObject.callAll()

    return z3const

def reportTest(formula):
    for k in range(1,2):
        const = runTest(formula, k)
        s = z3.Solver()
        s.add(const)
        print(s.to_smt2())
        s.set("timeout", 10000)
        checkResult = s.check()
        print(checkResult)
#         print(",".join(["f%s"%i, str(k), str(sizeAst(z3.And(const))+sizeAst(fullSep)), str(checkResult), str(etime1-stime1),str(etime2-stime2)]), file=fle)
#        print(s.to_smt2())
        print (s.model())


if __name__ == '__main__':
    print(testcase)
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        print(formula)
        reportTest(formula)
