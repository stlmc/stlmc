import z3
import io, os, sys
import gc, time, multiprocessing
from .base import *
from .stl import *
from .dRealHandler import *
from .z3Handler import *

sys.setrecursionlimit(10000)

class STLHandler:
    def __init__(self, model):
        self.model = model

    def runTest(self, formula, k):
        (modelconst,partition, formula) = self.model.modelCheck(formula, k)
        # z3
        try:
            z3model = [z3Obj(i) for i in modelconst]
            z3partition = [z3Obj(i) for i in partition]
            z3full = z3Obj(formula)
        except:
            z3const = []
       
        z3const = z3model + z3partition + [z3full]

        return (z3const,And(*modelconst).size(), And(*(partition + [formula])).size(), (formula.size() + 1))

    def reportTest(self, formula, filename, STLindex):
        with open(filename, 'a+') as fle:
            print("scheduleing f%s: "%STLindex + str(formula), file=fle)
        for k in range(1,2):
            with open(filename, 'a+') as fle:
                stime1 = time.process_time()
                self.model.reach(k)
                etime1 = time.process_time()
                (const, modelSize, formulasize, fullseparation) = self.runTest(formula, k)
                stime2 = time.process_time()
                s = z3.Solver()
                s.add(const)
                etime2 = time.process_time()
                checkResult = s.check()
               # checkResult = "test"
                print(filename + "  scheduleing f" + str(STLindex) + ": "+ str(k) + ",  " + str(checkResult))
                stime3 = time.process_time()
                print(",".join(["f%s"%STLindex,str(size(formula)), str(k), str(modelSize), str(formulasize), str(fullseparation), str(checkResult), str(etime1-stime1),str(etime2-stime2), str(stime3-etime2), str(stime3-stime2)]), file=fle)

if __name__ == '__main__':
#    print(testcase)
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        print(formula)
        reportTest(formula)




