import sys
import subprocess
from antlr4 import *
from core.syntax.modelLexer import modelLexer
from core.syntax.modelParser import modelParser
from core.modelVisitorImpl import modelVisitorImpl
from DataGenerator import *
import io, os, sys
import multiprocessing
import argparse

class ArgumentParser(argparse.ArgumentParser):

    def __init__(self):
        super(ArgumentParser, self).__init__(description='For more information. See below:')
        self.add_argument('-visualize', type = bool, default = False,
                            help='Start visualizing tool for the trace of the counterexample (default: false)')

    def error(self, message):
        """error(message: string)
        Prints a usage message incorporating the message to stderr and
        exits.
        If you override this in a subclass, it should not return -- it
        should either exit or raise an exception.
        """
        print(self._optionals)
#         if args.visualize:
#             print("ffff")
        self.print_usage(sys.stderr)
        args = {'prog': self.prog, 'message': message}

        #self.exit(2, ('%(prog)s: error: %(message)s\n') % args)


def module(title, stlModel, formula, k ,timeBound, dataGenerator, visualize, resultSave):
    modelName = os.path.splitext(os.path.basename(title))[0] 
    (result, cSize, fSize, generationTime, solvingTime, totalTime) = stlModel.modelCheck(modelName, formula, k, timeBound, False)

    # variable points bound, timeBound, goal
#    stlModel.reach(k, 60, Or(Not(Bool('xl2')), (Bool('xg3')))) 
#    stlModel.reach(k, 60, Bool('xl2'))

    if visualize:
        dataGenerator.data = stlModel.data
        dataGenerator.stackID = str(title).rsplit('/',1)[1].split(".")[0]
        dataGenerator.visualize()

    if resultSave:
        filename = "report" + "_" + modelName + "_" + str(formula) + ".txt"
        rel_path = str(os.path.abspath(os.curdir)) + "/reports/" + filename
        with open(rel_path, 'a+') as fle:
             print(",".join([str(k), str(cSize), str(fSize), str(result), generationTime, solvingTime, totalTime]), file=fle)

def modelCheck(fileName, lower, upper, step, timeBound, visualize, multy, resultSave):

    handlingModel = FileStream(fileName)
    lexer  = modelLexer(handlingModel)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.stlMC()
    stlMC =  modelVisitorImpl().visit(tree)
    dataGenerator = Api()
    workspace_info = dict()
    title = fileName
   
    for i in range(len(stlMC.getStlFormsList())):
        for k in range(lower, upper+1, step):
            formula = stlMC.getStlFormsList()[i]
            if multy:
                p = multiprocessing.Process(target = module, args=(title, stlMC, formula, k, timeBound, dataGenerator, visualize, resultSave))
                p.start()
            else:
                module(title, stlMC, formula, k, timeBound, dataGenerator, visualize, resultSave)


def main(args):
    modelList = list()
    if os.path.isdir(args.file):
        fileList = os.listdir(args.file)
        for item in fileList:
            if item.find('txt') is not -1:
                modelList.append(os.path.abspath(args.file) + "/" + item)
    elif os.path.isfile(args.file):
        modelList.append(args.file)
    else:
        raise ("file name is wrong")

    # create data directory for storing report files
    if args.save:
        if not os.path.exists(str(os.path.abspath(os.curdir)) + "/reports/"):
            os.makedirs(str(os.path.abspath(os.curdir)) + "/reports/")

    for m in modelList:
        if args.save:
            filename = "report" + "_" + os.path.splitext(os.path.basename(m))[0] + ".txt"
            rel_path = str(os.path.abspath(os.curdir)) + "/reports/" + filename
            with open(rel_path, 'w') as fle :
                print("k,ConstraintSize,TranslationSize,Result,generationTime,solvingTime, totalTime", file=fle)
        if args.upper == -1 :
            upper = args.lower
        else:
            upper = args.upper
        if args.visualize:
            visOut = subprocess.Popen(["../visualize/golang/main", "-v"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            stdout, stderr = visOut.communicate()
            print(stdout)
            print(stderr)
        modelCheck(m, args.lower, upper, args.step, args.timebound, args.visualize, args.multithread, args.save)
        

#'''
if __name__ == '__main__':
    parser = ArgumentParser()

    parser.add_argument('file', type = str, default = "", help="Type file or directory to process")

    parser.add_argument('-lower','-l', type = int, default = 1,
        help='model checking from the given lower bound (default: 1)')\

    parser.add_argument('-upper','-u', type = int, default = -1,
                help='model checking upto given upper bound (default: lower_bound)')

    parser.add_argument('-step','-s', type = int, default = 1,
                help='model checking at intervals of step in (lower, upper) (default: 1)')\

    parser.add_argument('-timebound','-tb', type = int, default = 60,
                            help='set time bound of model checking (default: 60)')\

    parser.add_argument('-multithread','-multy', type = bool, default = False,
                    help='run the given model using multithread (default: false)')

    parser.add_argument('-json', type = bool, default = False,
                    help='if a model have a counterexample, generate json format file for the trace of the counterexample (default: false)')

    parser.add_argument('-save', type = bool, default = False,
        help='save results of execution in report.txt (default: false)')

    isVis = False

    try:
        args = parser.parse_args()
        main(args)
        isVis = args.visualize
    except SystemExit:
        if isVis:
            print("yellllll")
#'''
