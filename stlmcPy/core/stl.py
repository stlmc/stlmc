from antlr4 import *
from stlmcPy.core.syntax.stlParser import stlParser
from stlmcPy.core.syntax.stlLexer import stlLexer
from .stlVisitorImpl import stlVisitorImpl

def parseFormula(fStr:str):
    lexer  = stlLexer(InputStream(fStr))
    stream = CommonTokenStream(lexer)
    parser = stlParser(stream)
    tree   = parser.formula()
    return stlVisitorImpl().visit(tree)
