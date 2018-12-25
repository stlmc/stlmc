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

def reportSatisfiable(model, goal):
    print("reachability checking: " + str(goal))
    result = model.reach(2, goal)
    print("    result: %s (constration size = %d)" % result)
        


if __name__ == '__main__':

    # pairs of a model, its benchmark parameters, and properties
    model1  = (M1.ThermostatPoly(),   20, 60, 4, M1.testcaseSTL,  M1.goal)

    configs = [model1]

    # create data directory if needed
    if not os.path.exists(str(os.path.abspath(os.curdir)) + "/data/"):
        os.makedirs(str(os.path.abspath(os.curdir)) + "/data/")
    
    # model checking runs
    for (model, bound, tmax, step, stlFormulas, reachGoal) in configs:        
        p = multiprocessing.Process(target = reportSatisfiable, args=(model, reachGoal))
        p.start()
