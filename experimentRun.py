import z3
import io, os, sys
import gc
import multiprocessing

from stlMC import *

import models.twoThermostatPoly as M1
import models.twoWatertankPoly as M2
import models.twoCarPoly as M3
import models.railroadPoly as M4
import models.twoBatteryPoly as M5
import models.twoThermostatLinear as M6
import models.twoWatertankLinear as M7
import models.twoCarLinear as M8
import models.railroadLinear as M9
import models.twoBatteryLinear as M10

def reportSatisfiable(model, formula, bound, step, timeBound, filename):
    for k in range(0, bound, step):
        print("  scheduleing " + str(formula) + " bound: " + str(k))
        (result, cSize, fSize, generationTime, solvingTime, totalTime) = model.modelCheck(formula, k, timeBound, False)
        with open(filename, 'a+') as fle:
            print(",".join([str(k), str(cSize), str(fSize), str(result), generationTime, solvingTime, totalTime]), file=fle)


if __name__ == '__main__':

    # pairs of a model, its benchmark parameters, and properties
    model1  = (M1.ThermostatPoly(),   21, 60, 4, M1.testcaseSTL,  M1.goal)
    model2  = (M2.WatertankPoly(),    21, 60, 4, M2.testcaseSTL,  M2.goal)
    model3  = (M3.CarPoly(),          21, 60, 4, M3.testcaseSTL,  M3.goal)
    model4  = (M4.RailroadPoly(),     21, 10, 4, M4.testcaseSTL,  M4.goal)
    model5  = (M5.BatteryPoly(),      21, 30, 4, M5.testcaseSTL,  M5.goal)

    model6  = (M6.ThermostatLinear(), 51, 100, 10, M6.testcaseSTL,  M6.goal)
    model7  = (M7.WatertankLinear(),  51, 100, 10, M7.testcaseSTL,  M7.goal)
    model8  = (M8.CarLinear(),        51,  60, 10, M8.testcaseSTL,  M8.goal)
    model9  = (M9.RailroadLinear(),   51,  10, 10, M9.testcaseSTL,  M9.goal)
    model10 = (M10.BatteryLinear(),   51,  30, 10, M10.testcaseSTL, M10.goal)

    configs = [model1, model2, model3, model4, model5, model6, model7, model8, model9, model10]

    # create data directory if needed
    if not os.path.exists(str(os.path.abspath(os.curdir)) + "/data/"):
        os.makedirs(str(os.path.abspath(os.curdir)) + "/data/")
    
    # model checking runs
    for (model, bound, tmax, step, stlFormulas, reachGoal) in configs:        
        for i in range(len(stlFormulas)):
            filename = str(type(model).__name__) + "f_" + str(i) + ".csv"
            rel_path = str(os.path.abspath(os.curdir)) + "/data/" + filename 
            with open(rel_path, 'w') as fle:
                print("k,ConstraintSize,TranslationSize,Result,generationTime,solvingTime, totalTime", file=fle)
            p = multiprocessing.Process(target = reportSatisfiable, args=(model, stlFormulas[i], bound, step, tmax, rel_path))
            p.start()
