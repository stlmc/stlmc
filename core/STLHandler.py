import z3
import io, os, sys
import gc, time, multiprocessing
from .base import *
from .stl import *
from .dRealHandler import *
from .z3Handler import *
from .interval import *

sys.setrecursionlimit(15000)

class STLHandler:
    def __init__(self, model):
        self.model = model

    def runTest(self, formula, k):
        (modelconst,partition, formula, fsSize) = self.model.modelCheck(formula, k)
        # z3
        try:
            z3model = [z3Obj(i) for i in modelconst]
            z3partition = [z3Obj(i) for i in partition]
            z3full = z3Obj(formula)
        except:
            z3const = []
       
        z3const = z3model + z3partition + [z3full]

        return (z3const,sizeAst(z3.And(*z3model)), sizeAst(z3.And(*(z3partition + [z3full]))), sizeAst(z3full), fsSize)

    def reportTest(self, formula, filename, STLindex, bound):
        for k in range(1,bound):
            with open(filename, 'a+') as fle:
                stime1 = time.process_time()
                (const, modelSize, formulasize, translationsize, fullSepSize) = self.runTest(formula, k)
                etime1 = time.process_time()
                s = z3.Solver()
                s.add(const)
                stime2 = time.process_time()
                print("  scheduleing f" + str(STLindex) + "_"+ str(k))
                checkResult = s.check()
               # checkResult = "test"
                print("  scheduleing f" + str(STLindex) + "_"+ str(k) + str(checkResult))
                etime2 = time.process_time()
                print(",".join(["f%s"%STLindex, str(k), str(modelSize), str(formulasize), str(translationsize), str(fullSepSize), str(checkResult), str(etime1-stime1),str(etime2-stime2)]), file=fle)

    def reachReport(self,m, filename,bound):
        for k in range(1,bound):
            with open(filename, 'a+') as fle:
                stime1 = time.process_time()
                const = m.reach(k)
                const = [z3Obj(i) for i in const]
                etime1 = time.process_time()
                s = z3.Solver()
                s.add(const)
                stime2 = time.process_time()
                print("  reach_"+ str(k))
                checkResult = s.check()
               # checkResult = "test"
                print("  reach_"+ str(k) + str(checkResult))
                etime2 = time.process_time()
                print(",".join([str(k), str(sizeAst(z3.And(const))),  str(checkResult), str(etime1-stime1),str(etime2-stime2)]), file=fle)

if __name__ == '__main__':
#    print(testcase)
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        print(formula)
        reportTest(formula)




