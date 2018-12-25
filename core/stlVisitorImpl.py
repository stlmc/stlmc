from antlr4 import *
from .syntax.stlParser import stlParser
from .syntax.stlVisitor import stlVisitor
from .formula import *

class stlVisitorImpl(stlVisitor):

    # Visit a parse tree produced by stlParser#leftEnd.
    def visitLeftEnd(self, ctx:stlParser.LeftEndContext):
        return (not ctx.LPAREN(), float(ctx.value.text))


    # Visit a parse tree produced by stlParser#rightEnd.
    def visitRightEnd(self, ctx:stlParser.RightEndContext):
        return (not ctx.RPAREN(), float(ctx.value.text))


    # Visit a parse tree produced by stlParser#interval.
    def visitInterval(self, ctx:stlParser.IntervalContext):
        if ctx.EQUAL():
            number = float(ctx.NUMBER().getText())
            return Interval(True, number, True, number)
        else:
            left = self.visit(ctx.leftEnd())
            right = self.visit(ctx.rightEnd())
            return Interval(left[0], left[1], right[0], right[1])


    # Visit a parse tree produced by stlParser#parenFormula.
    def visitParenFormula(self, ctx:stlParser.ParenFormulaContext):
        return self.visit(ctx.formula())


    # Visit a parse tree produced by stlParser#constant.
    def visitConstant(self, ctx:stlParser.ConstantContext):
        return ConstantFormula(ctx.getText())


    # Visit a parse tree produced by stlParser#binaryTemporalFormula.
    def visitBinaryTemporalFormula(self, ctx:stlParser.BinaryTemporalFormulaContext):
        time = self.visit(ctx.interval())
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        return {'U': UntilFormula, 'R': ReleaseFormula}[ctx.op.text](time, universeInterval, left, right)


    # Visit a parse tree produced by stlParser#proposition.
    def visitProposition(self, ctx:stlParser.PropositionContext):
        return PropositionFormula(ctx.getText())


    # Visit a parse tree produced by stlParser#binaryFormula.
    def visitBinaryFormula(self, ctx:stlParser.BinaryFormulaContext):
        op = ctx.op.text
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        if op == '->':
            return ImpliesFormula(left,right)
        elif op == '/\\':
            return AndFormula([left,right])
        elif op == '\\/':
            return OrFormula([left,right])
        else:
            raise "something wrong"


    # Visit a parse tree produced by stlParser#unaryTemporalFormula.
    def visitUnaryTemporalFormula(self, ctx:stlParser.UnaryTemporalFormulaContext):
        time = self.visit(ctx.interval())
        child = self.visit(ctx.formula())
        return {'[]': GloballyFormula, '<>': FinallyFormula}[ctx.op.text](time, universeInterval, child)


    # Visit a parse tree produced by stlParser#unaryFormula.
    def visitUnaryFormula(self, ctx:stlParser.UnaryFormulaContext):
        child = self.visit(ctx.formula())
        return {'~': NotFormula}[ctx.op.text](child)



del stlParser
