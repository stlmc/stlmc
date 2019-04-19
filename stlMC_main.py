import sys
from antlr4 import *
from core.syntax.modelLexer import modelLexer
from core.syntax.modelParser import modelParser
from core.modelVisitorImpl import modelVisitorImpl
import io, os, sys


def main(argv):
    input = FileStream(argv[1])
    lexer  = modelLexer(input)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.stlMC()
    stlMC =  modelVisitorImpl().visit(tree)

    # create data directory if needed
    if not os.path.exists(str(os.path.abspath(os.curdir)) + "/data/"):
        os.makedirs(str(os.path.abspath(os.curdir)) + "/data/")

    for i in range(len(stlMC.getStlFormsText())):
        filename = str("linearThermo") + "f_" + str(i) + ".csv"
        rel_path = str(os.path.abspath(os.curdir)) + "/data/" + filename
        with open(rel_path, 'w' ) as fle:
            print("k,ConstraintSize,TranslationSize,Result,generationTime,solvingTime, totalTime", file=fle)
        #args : (0, bound, step)
        for k in range(1, 2, 2):
            strFormula = stlMC.getStlFormsText()[i]
            formula = stlMC.getStlFormsList()[i]
            print("Scheduleing " + strFormula + " bound: " + str(k))
            timeBound = 60
            (result, cSize, fSize, generationTime, solvingTime, totalTime) = stlMC.modelCheck(formula, k, timeBound, False)
            visualize = stlMC.getSpecificModel()
#            '''
            print(visualize.getVarsId())
            print(visualize.getContValues())
            print(visualize.getTauValues())
            print(visualize.getODE())
            print(visualize.getProposition())
            visualize.visualize()
#            '''
            with open(rel_path, 'a+') as fle:
                print(",".join([str(k), str(cSize), str(fSize), str(result), generationTime, solvingTime, totalTime]), file=fle)

if __name__ == '__main__':
    main(sys.argv)
