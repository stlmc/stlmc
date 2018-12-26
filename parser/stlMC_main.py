import sys
from antlr4 import *
from modleLexer import modelLexer
from modelParser import modelParser
from modelVisitorImpl import modelVisitorImpl

def parseModel(fStr:str):
    input = FileStream(str)
    lexer  = modelLexer(input)
    stream = CommonTokenStream(lexer)
    parser = modelParser(stream)
    tree   = parser.model()
    modelVisitorImpl().visit(tree)

