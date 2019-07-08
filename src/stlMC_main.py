import sys
from antlr4 import *
from core.syntax.modelLexer import modelLexer
from core.syntax.modelParser import modelParser
from core.modelVisitorImpl import modelVisitorImpl
from DataGenerator import *
import io, os, sys
from visualize import *
import multiprocessing

def module(title, stlModel, formula, k ,timeBound, dataGenerator):
    (result, cSize, fSize, generationTime, solvingTime, totalTime) = stlModel.modelCheck(formula, k, timeBound, False)
    dataGenerator.data = stlModel.data
    dataGenerator.stackID = str(title).rsplit('/',1)[1].split(".")[0]
    dataGenerator.visualize()


def main(argv):
    input = FileStream(argv[1])
    lexer  = modelLexer(input)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.stlMC()
    stlMC =  modelVisitorImpl().visit(tree)
    dataGenerator = Api()
    path_dir="../visualize/src/DataDir/"
    file_list = os.listdir(path_dir)
    print(file_list)
    workspace_info = dict()
    title = argv[1]

    workspace_info["file_list"] = file_list

    import json
    f = open(("../visualize/src/DataDir/.workspace_info.json"), "w")
    json.dump(workspace_info, f)
    f.close()

    for i in range(len(stlMC.getStlFormsList())):
        #args : (0, bound, step)
        for k in range(2, 3, 10):
            formula = stlMC.getStlFormsList()[i]
            print("Scheduleing " + str(formula) + " bound: " + str(k))
            timeBound = 60
            p = multiprocessing.Process(target = module, args=(title, stlMC, formula, k, timeBound, dataGenerator))
            p.start()
            '''
            print(visualize.getVarsId())
            print(visualize.getModesId())
            #print(visualize.getContValues())
            print(visualize.getTauValues())
            print(visualize.getODE())
            print(visualize.getProposition())
            visualize.visualize()
            '''

if __name__ == '__main__':
    main(sys.argv)
