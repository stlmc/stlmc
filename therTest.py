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
    for k in range(0, bound + 1, step):
        print("  scheduleing " + str(formula) + " bound: " + str(k))
        (result, cSize, fSize, generationTime, solvingTime, totalTime) = model.modelCheck(formula, k, timeBound, False)
        with open(filename, 'a+') as fle:
            print(",".join([str(k), str(cSize), str(fSize), str(result), generationTime, solvingTime, totalTime]), file=fle)


if __name__ == '__main__':

    # pairs of a model, its benchmark parameters, and properties
    model6  = (M6.ThermostatLinear(),   1, 60, 4, M6.testcaseSTL,  M6.goal)

    configs = [model6]

    for (model, bound, tmax, step, stlFormulas, reachGoal) in configs:
        model.modelCheck(stlFormulas[0], bound, tmax, False)
   

    '''
    # create data directory if needed
    if not os.path.exists(str(os.path.abspath(os.curdir)) + "/data/"):
        os.makedirs(str(os.path.abspath(os.curdir)) + "/data/")
    
    # model checking runs
    for (model, bound, tmax, step, stlFormulas, reachGoal) in configs:        
        for i in [2]: 
            filename = str(type(model).__name__) + "f_" + str(i) + ".csv"
            rel_path = str(os.path.abspath(os.curdir)) + "/data/" + filename 
            with open(rel_path, 'w') as fle:
                print("k,ConstraintSize,TranslationSize,Result,generationTime,solvingTime, totalTime", file=fle)
            p = multiprocessing.Process(target = reportSatisfiable, args=(model, stlFormulas[i], bound, step, tmax, rel_path))
            p.start()
    '''
