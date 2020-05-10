import sys, gc, time
import io, os
import stlmcPy.core.partition as PART
import stlmcPy.core.separation as SEP
from stlmcPy.core.randomSTL import *
import stlmcPy.core.encoding as ENC
from stlmcPy.core.z3Handler import *
from stlmcPy.core.yicesHandler import *
from stlmcPy.core.stl import *
from testcase2 import testcase

sys.setrecursionlimit(30000)

def runTest(formula, k, solver):
    stime = time.process_time()
    fsize = 0

    baseP = PART.baseCase(k)
    (partition, sepMap, partitionConsts) = PART.guessPartition(formula, baseP)
    fs = SEP.fullSeparation(formula, sepMap)

    baseV = ENC.baseEncoding(partition, baseP) 

    formulaConst = ENC.valuation(fs[0], fs[1], ENC.Interval(True, 0.0, True, 0.0), baseV)
    
    allConsts = partitionConsts + [formulaConst]
    fsize += sum([ENC.size(f) for f in [fs[0]] + list(fs[1].values())])

    etime1 = time.process_time()
    if solver == 'z3':
        (result, cSize, model) = z3checkSat(allConsts, 'LRA')
    elif solver == 'yices':
        (result, cSize, model) = yicescheckSat(allConsts, 'QF_LRA')

    etime2 = time.process_time()


    generationTime = round((etime1 - stime), 4)
    solvingTime = round((etime2 - etime1), 4)
    totalTime = round((etime2 - stime), 4)

   
    return (result, cSize, fsize, str(generationTime), str(solvingTime), str(totalTime))

def saveResult(formula, result, k, cSize, fSize, generation, solving, totalTime, nested, numTemp, solver):
    filename = "report2" + "_" + solver + ".csv"
    rel_path = str(os.path.abspath(os.curdir)) + "/" + filename
    with open(rel_path, 'a+') as fle:
        print(",".join([str(k), str(cSize), str(fSize), str(result), generation, solving, totalTime, str(nested), str(numTemp), str(nested+numTemp)]),
                  file=fle)
    print("---------------------------------------------------------------------------\n")
    print("STL formula : \"" + str(formula) + "\"")
    print("Result : " + str(result) + ", Variable point bound : " + str(k))
    print("Constraint size : " + str(cSize) + ", Formula size : " + str(fSize))
    print("Execution Time(sec) : " + totalTime + "\n")
    print("---------------------------------------------------------------------------\n")

def testGen(solver):
    error = 0
    i = 1
    # fs is proposition size
    filename = "report2" + "_" + solver + ".csv"
    rel_path = str(os.path.abspath(os.curdir)) + "/" + filename
    if not os.path.isfile(rel_path):
        with open(rel_path, 'a+') as fle:
            print("k,ConstraintSize,TranslationSize,Result,generationTime,solvingTime, totalTime, nested, numTemp, basis",
                                  file=fle)
 
    
    '''              
    for fs in range(5, 10):
        for c in range(3):
            formula = randFormula(fs,5)
            print(formula)
    '''
    for i in range(len(testcase)):
        formula = parseFormula(testcase[i])
        #print(size(formula))
        #print(numTemp(formula))
        #print(formula.temporalHeight())
        print("index : " + str(i))
        for k in range (10, 61, 10):
            (result, cSize, fSize, generation, solving, totalTime) = runTest(formula, k, solver)
            saveResult(formula, result, k, cSize, fSize, generation, solving, totalTime, formula.temporalHeight(), numTemp(formula), solver)


if __name__ == '__main__':
    testGen('z3')
   # testGen('yices')

