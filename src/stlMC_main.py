import sys
from antlr4 import *
from core.syntax.modelLexer import modelLexer
from core.syntax.modelParser import modelParser
from core.modelVisitorImpl import modelVisitorImpl
from DataGenerator import *
import io, os, sys
import multiprocessing

def module(title, stlModel, formula, k ,timeBound, dataGenerator):
    (result, cSize, fSize, generationTime, solvingTime, totalTime) = stlModel.modelCheck(formula, k, timeBound, False)

    # variable points bound, timeBound, goal
#    stlModel.reach(k, 60, Or(Not(Bool('xl2')), (Bool('xg3')))) 
#    stlModel.reach(k, 60, Bool('xl2'))
#    '''
    dataGenerator.data = stlModel.data
    dataGenerator.stackID = str(title).rsplit('/',1)[1].split(".")[0]
    dataGenerator.visualize()
#    '''

def main(argv):
    input = FileStream(argv[1])
    lexer  = modelLexer(input)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.stlMC()
    stlMC =  modelVisitorImpl().visit(tree)
    dataGenerator = Api()
    workspace_info = dict()
    title = argv[1]

    for i in range(len(stlMC.getStlFormsList())):
        #args : (0, bound, step)
        for k in range(6, 7, 5):
            formula = stlMC.getStlFormsList()[i]
            timeBound = 60
            module(title, stlMC, formula, k, timeBound, dataGenerator)
#            p = multiprocessing.Process(target = module, args=(title, stlMC, formula, k, timeBound, dataGenerator))
#            p.start()

if __name__ == '__main__':
    main(sys.argv)
