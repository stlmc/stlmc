from Thermostat.twoThermostatPoly import *
from Watertank.twoWatertankPoly import *
from Car.twoCar import *

def report(Object, filename, bound):
    Object.reachReport(m, str(filename)+ "Reach", bound+1)

if __name__ == '__main__':
    model1 = Thermostat()
    model2 = Watertank()
    model3 = Car()

    modelPoly = [model1, model2]
    modelLinear = [model3]
    
    for m in (modelPoly + modelLinear):
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
        p = multiprocessing.Process(target = report, args=(stlObject, m.filename, bound))
        p.start()
   



