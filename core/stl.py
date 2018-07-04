
from antlr4 import *
from .syntax.stlLexer import stlLexer
from .syntax.stlParser import stlParser
from .stlVisitorImpl import stlVisitorImpl

def parseFormula(fStr:str):
    lexer  = stlLexer(InputStream(fStr))
    stream = CommonTokenStream(lexer)
    parser = stlParser(stream)
    tree   = parser.formula()
    return stlVisitorImpl().visit(tree)
