from Thermostat.twoThermostatLinear import *
from Watertank.twoWatertankLinear import *

def report(Object, formula, filename, i, bound):
    Object.reportTest(formula, str(filename) + "f_"+str(i), i, bound+1)
    Object.reachReport(m, str(filename)+ "Reach", bound+1)

if __name__ == '__main__':
    model1 = Thermostat()
    model2 = Watertank()
    model = [model1, model2]
    for m in model: 
        bound = 100
        stlObject = STLHandler(m)
        with open(str(m.filename)+ "Reach", 'w') as fle:
            print("k,ModelConstraintSize,Result,Generation,Solving", file=fle)
        for i in range(len(m.stl)):
            with open(str(m.filename) + "f_"+str(i), 'w') as fle:
                print("id,k,ModelConstraintSize,FormulaConstraintSize,TranslationSize,FullSeparation,Result,Generation,Solving", file=fle)
            formula = parseFormula(m.stl[i])
            p = multiprocessing.Process(target = report, args=(stlObject, formula, m.filename, i, bound))
            p.start()
   



