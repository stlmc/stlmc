# Generated from vila.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .vilaParser import vilaParser
else:
    from vilaParser import vilaParser

# This class defines a complete generic visitor for a parse tree produced by vilaParser.

class vilaVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by vilaParser#expression.
    def visitExpression(self, ctx:vilaParser.ExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by vilaParser#statement.
    def visitStatement(self, ctx:vilaParser.StatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by vilaParser#comment.
    def visitComment(self, ctx:vilaParser.CommentContext):
        return self.visitChildren(ctx)



del vilaParser