import sys
from antlr4 import *
from .vila.vilaLexer import vilaLexer
from .vila.vilaParser import vilaParser
from .vila.vilaStlMCVisitor import vilaStlMCVisitor

class VilaInterpreter():

    def __init__(self):
        self.var_name = ""

    # _readVila for internal supported
    # var_assn: ode variable list in dictionary form
    # e.g) z = { 'x1': 0, 'x2' :1 }
    def _readVila(self, var_assn, vila_string:str):
        input = InputStream(vila_string)
        lexer = vilaLexer(input)
        stream = CommonTokenStream(lexer)
        parser = vilaParser(stream)
        tree = parser.statement()
        vilaVisitor = vilaStlMCVisitor(var_assn)
        vila = vilaVisitor.visit(tree)
        self.var_name = vilaVisitor.var_name
        return vila

    def vila2model(self, var_assn, vila_string_list:list):
        res = dict()
        for vila_string in vila_string_list:
            v = self._readVila(var_assn, vila_string)
            res[self.var_name]=v.result
        return res

