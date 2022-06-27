from antlr4.error.ErrorListener import ErrorListener


class StlmcErrorListener(ErrorListener):
    def __init__(self):
        self.name = ""

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        raise SyntaxError("in \"{}\" line {}:{} {}".format(self.name, line, column, msg))
