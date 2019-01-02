import sys
from antlr4 import *
from modelLexer import modelLexer
from modelParser import modelParser
from modelVisitorImpl import modelVisitorImpl

'''
def parseModel(fStr:str):
    input = FileStream(str)
    lexer  = modelLexer(input)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.stlMC()
    modelVisitorImpl().visit(tree)
'''

def main(argv):
    input = FileStream(argv[1])
    lexer  = modelLexer(input)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.stlMC()
    modelVisitorImpl().visit(tree)

if __name__ == '__main__':
    main(sys.argv)
