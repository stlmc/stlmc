from antlr4 import *
from .vilaParser import vilaParser
from .vilaVisitor import vilaVisitor
from .vilaMath import *

class vilaStlMCVisitor(vilaVisitor):

    def __init__(self, ode_var):
        self.expression = list()
        self.ode_var = ode_var
        self.var_name = ""

    def visitStatement(self, ctx:vilaParser.StatementContext):
        return self.visitExpression(ctx.expression())

    def visitExpression(self, ctx:vilaParser.ExpressionContext):
        # print("visitExpression: " + ctx.getText())
        exp = Expression(self.ode_var)
        if ctx.operator:
            if ctx.operator.text == '=':
                self.var_name = ctx.expression()[0].getText()
                exp.eq(self.visitExpression(ctx.expression()[1]).result)
            else:
                exp.operator(ctx.operator.text, self.visitExpression(ctx.expression()[0]).result, self.visitExpression(ctx.expression()[1]).result)
        if ctx.uniop:
            if ctx.VARIABLE():
                exp.uniopvar(ctx.VARIABLE().getText())
            else:
                exp.uniopnum(ctx.NUMBER().getText())
        elif ctx.value:
            if ctx.VARIABLE():
                exp.variable(ctx.VARIABLE().getText())
            else:
                exp.number(ctx.NUMBER().getText())
        return exp

    def visitComment(self, ctx:vilaParser.CommentContext):
        return self.visitChildren(ctx)

