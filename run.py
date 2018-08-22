from Thermostat.twoThermostatPoly import *
from Thermostat.twoThermostatLinear import *
from Watertank.twoWatertankPoly import *
from Watertank.twoWatertankLinear import *
from Car.twoCarLinear import *
from Car.twoCarPoly import *
from Railroad.railroadLinear import *
from Railroad.railroadPoly import *
from Battery.twoBatteryPoly import *
from Battery.twoBatteryLinear import *


def reportTest(Object, formula, filename, i, bound):
    Object.reportTest(formula, str(filename) + "f_"+str(i) + ".csv", i, bound+1)

def reachTest(Object,  filename, bound):
    Object.reachReport(m, str(filename)+ "Reach.csv", bound+1)


if __name__ == '__main__':
    model1 = ThermostatPoly()
    model2 = WatertankPoly()
    model3 = CarPoly()
    model4 = RailroadPoly()
    model5 = BatteryPoly()

    model6 = ThermostatLinear()
    model7 = WatertankLinear()
    model8 = CarLinear()
    model9 = RailroadLinear()
    model10 = BatteryLinear()
    

    modelPoly = [model1, model2, model3, model4, model5]
    modelLinear = [model6, model7, model8, model9, model10]
    
    for m in (modelPoly + modelLinear):
        if m in modelPoly:
            bound = 50
        elif m in modelLinear:
            bound = 100
        else:
            print("error")
            bound = 0
        stlObject = STLHandler(m)
        with open(str(m.filename)+ "Reach.csv", 'w') as fle:
            print("k,ModelConstraintSize,Result,Generation,Solving", file=fle)
        for i in range(len(m.stl)):
            with open(str(m.filename) + "f_"+str(i) + ".csv", 'w') as fle:
                print("id,k,ModelConstraintSize,FormulaConstraintSize,TranslationSize,FullSeparation,Result,Generation,Solving", file=fle)
            formula = parseFormula(m.stl[i])
            p = multiprocessing.Process(target = reportTest, args=(stlObject, formula, m.filename, i, bound))
            p.start()
        q = multiprocessing.Process(target = reachTest, args=(stlObject, m.filename, bound))
        q.start()
   



