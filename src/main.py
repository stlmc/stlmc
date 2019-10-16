import sys
import logging
import logging.handlers
import subprocess
from antlr4 import *
from core.syntax.modelLexer import modelLexer
from core.syntax.modelParser import modelParser
from core.modelVisitorImpl import modelVisitorImpl
from DataGenerator import *
import io, os, sys
import multiprocessing
import argparse
from yices import *

def str2bool(v):
    if v.lower() in ('yes', 'true', 't', 'y', '1'):
        return True
    elif v.lower() in ('no', 'false', 'f', 'n', '0'):
        return False
    else:
        raise argparse.ArgumentTypeError('Boolean value expected.')


def module(title, stlModel, formula, k ,timeBound, dataGenerator, json, resultSave, solver):
    modelName = os.path.splitext(os.path.basename(title))[0] 
    (result, cSize, fSize, generationTime, solvingTime, totalTime) = stlModel.modelCheck(modelName, formula, k, timeBound, solver, False)

    if json:
        dataGenerator.data = stlModel.data
        dataGenerator.stackID = str(title).rsplit('/',1)[1].split(".")[0]
        dataGenerator.solver = solver
        dataGenerator.visualize()

    if resultSave:
        filename = "report" + "_" + modelName + "_" + str(formula) + ".txt"
        rel_path = str(os.path.abspath(os.curdir)) + "/reports/" + filename
        with open(rel_path, 'a+') as fle:
             print(",".join([str(k), str(cSize), str(fSize), str(result), generationTime, solvingTime, totalTime]), file=fle)


def modelCheck(fileName, lower, upper, step, timeBound, json, multy, resultSave, solver, stlLogger):

    handlingModel = FileStream(fileName)
    lexer  = modelLexer(handlingModel)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.stlMC()
    stlMC =  modelVisitorImpl().visit(tree)
    dataGenerator = Api(stlLogger)
    workspace_info = dict()
    title = fileName

    for i in range(len(stlMC.getStlFormsList())):
        for k in range(lower, upper+1, step):
            formula = stlMC.getStlFormsList()[i]
            if multy:
                p = multiprocessing.Process(target = module, args=(title, stlMC, formula, k, timeBound, dataGenerator, json, resultSave, solver))
                p.start()
            else:
                module(title, stlMC, formula, k, timeBound, dataGenerator, json, resultSave, solver)

def main(args, stlLogger):
    modelList = list()
    try:
        if os.path.isdir(args.file):
            fileList = os.listdir(args.file)
            for item in fileList:
                if item.find('txt') is not -1:
                    modelList.append(os.path.abspath(args.file) + "/" + item)
        elif os.path.isfile(args.file):
            modelList.append(args.file)
        else:
            stlLogger.error("file name is wrong")
            raise ("file name is wrong")

        save = False if args.save is None else args.save
        lower = 1 if args.lower is None else args.lower
        upper = lower if args.upper is None else args.upper
        visualize = False if args.visualize is None else args.visualize
        json = visualize if args.json is None else args.json
        if visualize and not json:
            print("automatically change json option to true")
            json = True

        multithread = False if args.multithread is None else args.multithread
        timebound = 60 if args.timebound is None else args.timebound
        step = 1 if args.step is None else args.step

        # create data directory for storing report files
        if save:
            if not os.path.exists(str(os.path.abspath(os.curdir)) + "/reports/"):
                os.makedirs(str(os.path.abspath(os.curdir)) + "/reports/")

        for m in modelList:
            if save:
                filename = "report" + "_" + os.path.splitext(os.path.basename(m))[0] + ".txt"
                rel_path = str(os.path.abspath(os.curdir)) + "/reports/" + filename
                with open(rel_path, 'w') as fle :
                    print("k,ConstraintSize,TranslationSize,Result,generationTime,solvingTime, totalTime", file=fle)
            modelCheck(m, lower, upper, step, timebound, json, multithread, save, args.solver.lower(), stlLogger)

        if visualize:
            try:
                if not(os.path.isdir("./DataDir")):
                    os.makedirs(os.path.join("./DataDir"))
            except OSError as e:
                if e.errno != errno.EEXIST:
                    stlLogger.error("Failed to create directory!!!!!")
                    raise
            subprocess.call(["../visualize/golang/main", "-v"])
    except Exception as ex:
        if not all(argi is None for argi in [args.lower, args.upper, args.step, args.multithread, args.timebound, args.save, args.json]):
            print("\nNeed to provide file name!")
            print("Type [-h] to see help.")
        elif args.visualize:
            try:
                if not(os.path.isdir("./DataDir")):
                    os.makedirs(os.path.join("./DataDir"))
            except OSError as e:
                if e.errno != errno.EEXIST:
                    stlLogger.error("Failed to create directory!!!!!")
                    raise
            subprocess.call(["../visualize/golang/main", "-v"])
        else:
            raise

if __name__ == '__main__':
    # setting logger
    stlLogger = logging.getLogger("StlMC")
    stlLogger.setLevel(logging.NOTSET)


    formatter = logging.Formatter('[%(levelname)s ==> %(filename)s:%(lineno)s] %(asctime)s >> %(message)s')
    try:
        if not(os.path.isdir("./log")):
            os.makedirs(os.path.join("./log"))
    except OSError as e:
        if e.errno != errno.EEXIST:
            stlLogger.error("Failed to create directory!!!!!")
            raise

    log_file_count = 2000
    fileHandler = logging.handlers.TimedRotatingFileHandler(filename="./log/main.log"
    ,when='s', interval=1, backupCount=log_file_count)
    streamHandler = logging.StreamHandler()

    fileHandler.setFormatter(formatter)
    streamHandler.setFormatter(formatter)

    stlLogger.addHandler(fileHandler)
    stlLogger.addHandler(streamHandler)

    stlLogger.info("StlMC main start")


    parser = argparse.ArgumentParser(description='For more information. See below:')

    parser.add_argument('file', nargs='?', type = str, help="Type file or directory to process")

    parser.add_argument('-lower','-l', type = int,
        help='model checking from the given lower bound (default: 1)')\

    parser.add_argument('-upper','-u', type = int,
                help='model checking upto given upper bound (default: lower_bound)')

    parser.add_argument('-step','-s', type = int,
                help='model checking at intervals of step in (lower, upper) (default: 1)')\

    parser.add_argument('-timebound','-tb', type = int,
                            help='set time bound of model checking (default: 60)')\

    parser.add_argument('-multithread','-multy', type = str2bool,
                    help='run the given model using multithread (default: false)')

    parser.add_argument('-solver', type = str, default = 'z3',
            help='run the model using given smt solver, support \" {Yices, Z3} \" (default: z3)')

    parser.add_argument('-visualize', type = str2bool,
                                help='Start visualizing tool for the trace of the counterexample (default: false)')

    parser.add_argument('-json', type = str2bool,
                    help='if a model have a counterexample, generate json format file for the trace of the counterexample (default: false)')

    parser.add_argument('-save', type = str2bool,
        help='save results of execution in report.txt (default: false)')

    parser.add_argument('-log', type = str2bool, default="False",
            help='show logging information (default: false)')

    try:
        args = parser.parse_args()
        if args.log:
            stlLogger.setLevel(logging.INFO)
        main(args, stlLogger)
    except SystemExit:
        stlLogger.debug("System error")

