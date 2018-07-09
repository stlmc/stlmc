import z3
import io, os, sys
import gc, time, multiprocessing
from .base import *
from .stl import *
from .dRealHandler import *
from .z3Handler import *

sys.setrecursionlimit(10000)

class STLHandler:
    def __init__(self, model, testcase):
        self.model = model
        self.testcase = testcase

    def runTest(self, formula, k):
        const = self.model.modelCheck(formula, k)
        # z3
        try:
            z3const = [z3Obj(i) for i in const]
        except:
            z3const = []
        # dReal
        dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
        dRealname = dRealname[:-3]
        dRealname += '_' + str(k) + '.smt2'

        with open(dRealname, 'w') as fle:
            printObject = dRealHandler(const, fle, self.model.varList, self.model.variables, self.model.flowDict, self.model.mode, self.model.time, k)
            printObject.addConst(const)
            printObject.callAll()

        return z3const

    def reportTest(self, formula):
        for k in range(2,3):
            const = self.runTest(formula, k)
            s = z3.Solver()
            s.add(const)
    #        print(s.to_smt2())
            s.set("timeout", 10000)
            checkResult = s.check()
            print(checkResult)
    #         print(",".join(["f%s"%i, str(k), str(sizeAst(z3.And(const))+sizeAst(fullSep)), str(checkResult), str(etime1-stime1),str(etime2-stime2)]), file=fle)
    #        print(s.to_smt2())
    #        print (s.model())

    def generateSTL(self):
        output = io.StringIO()
        const = self.model.reach(3)
        printObject = dRealHandler(const, output, self.model.varList, self.model.variables, self.model.flowDict, self.model.mode, self.model.time, 0)
        printObject.callAll()
    #    print (output.getvalue())
        dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
        dRealname = dRealname[:-3]
        dRealname += '_noSTL.smt2'
        f = open(dRealname, 'w')
        f.write(output.getvalue())
        f.close()

        for i in range(len(self.testcase)):
            formula = parseFormula(self.testcase[i])
            print(formula)
            self.reportTest(formula)

if __name__ == '__main__':
#    print(testcase)
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        print(formula)
        reportTest(formula)




