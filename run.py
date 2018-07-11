from Thermostat.twoThermostat import *
from Watertank.twoWatertank import *
from Car.twoCar import *
from Railroad.railroad import *
from Battery.twoBattery import *

def report(Object, formula, filename, i):
    Object.reportTest(formula, filename,i)

if __name__ == '__main__':
    model1 = Thermostat()
    model2 = Watertank()
    model3 = Car()
    model4 = Railroad()
    model5 = Battery()

    model = [model1, model2, model3, model4, model5]
    model = [model2]
    for m in model:
        with open(m.filename, 'w') as fle:
            print("id,STLformulaSize,k,ModelConstraintSize,FormulaSize,FullSeparation,Result,Reach,Generation,Solving,Total", file=fle)
        for i in range(len(m.stl)):
            formula = parseFormula(m.stl[i])
            stlObject = STLHandler(m)
            stlObject.reportTest(formula, m.filename, i)
            print(m.filename)
            print(m.stl[i])
#            p = multiprocessing.Process(target = report, args=(stlObject, formula, m.filename, i))
#            p.start()


