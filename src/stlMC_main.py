import sys
from antlr4 import *
from core.syntax.modelLexer import modelLexer
from core.syntax.modelParser import modelParser
from core.modelVisitorImpl import modelVisitorImpl
import io, os, sys
from visualize import *

def main(argv):
    input = FileStream(argv[1])
    lexer  = modelLexer(input)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.stlMC()
    stlMC =  modelVisitorImpl().visit(tree)
    dataGenerator = Api()

    for i in range(len(stlMC.getStlFormsList())):
        #args : (0, bound, step)
        for k in range(4, 5, 2):
            formula = stlMC.getStlFormsList()[i]
            print("Scheduleing " + str(formula) + " bound: " + str(k))
            timeBound = 60
            (result, cSize, fSize, generationTime, solvingTime, totalTime) = stlMC.modelCheck(formula, k, timeBound, False)
#            visualize = stlMC.getSpecificModel()
            dataGenerator.data = stlMC.data
            dataGenerator.stackID = str(argv[1]).rsplit('/',1)[1].split(".")[0]
            dataGenerator.visualize()
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
