from Railroad.railroadPoly import *
from Railroad.railroad import *

def reportTest(Object, formula, filename, i, bound):
    Object.reportTest(formula, str(filename) + "f_"+str(i), i, bound+1)

def reachTest(Object,  filename, bound):
    Object.reachReport(m, str(filename)+ "Reach", bound+1)

if __name__ == '__main__':
    model1 = PolyRailroad()
    model2 = Railroad()

    modelPoly = [model1]
    modelLinear = [model2]
    for m in modelPoly + modelLinear: 
        if m in modelPoly:
            bound = 50
        elif m in modelLinear:
            bound = 100
        else:
            print("error")
            bound = 0
        stlObject = STLHandler(m)
        with open(str(m.filename)+ "Reach", 'w') as fle:
            print("k,ModelConstraintSize,Result,Generation,Solving", file=fle)
        for i in range(len(m.stl)):
            with open(str(m.filename) + "f_"+str(i), 'w') as fle:
                print("id,k,ModelConstraintSize,FormulaConstraintSize,TranslationSize,FullSeparation,Result,Generation,Solving", file=fle)
            formula = parseFormula(m.stl[i])
            p = multiprocessing.Process(target = reportTest, args=(stlObject, formula, m.filename, i, bound))
            p.start()
            q = multiprocessing.Process(target = reachTest, args=(stlObject, m.filename, bound))
            q.start()
   



