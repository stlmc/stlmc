import sys
from antlr4 import *
from vila.vilaLexer import vilaLexer
from vila.vilaParser import vilaParser
from vila.vilaStlMCVisitor import vilaStlMCVisitor


def llmain(argv):
    print("hello")
    input = FileStream(argv[1])
    lexer = vilaLexer(input)
    stream = CommonTokenStream(lexer)
    parser = vilaParser(stream)
    tree = parser.statement()
    vilaVisitor = vilaStlMCVisitor({'x1':11.0}).visit(tree)
    print(vilaVisitor.result)

llmain(sys.argv)
