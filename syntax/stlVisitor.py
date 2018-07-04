# Generated from stl.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .stlParser import stlParser
else:
    from stlParser import stlParser

# This class defines a complete generic visitor for a parse tree produced by stlParser.

class stlVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by stlParser#leftEnd.
    def visitLeftEnd(self, ctx:stlParser.LeftEndContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#rightEnd.
    def visitRightEnd(self, ctx:stlParser.RightEndContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#interval.
    def visitInterval(self, ctx:stlParser.IntervalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#parenFormula.
    def visitParenFormula(self, ctx:stlParser.ParenFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#constant.
    def visitConstant(self, ctx:stlParser.ConstantContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#binaryTemporalFormula.
    def visitBinaryTemporalFormula(self, ctx:stlParser.BinaryTemporalFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#proposition.
    def visitProposition(self, ctx:stlParser.PropositionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#binaryFormula.
    def visitBinaryFormula(self, ctx:stlParser.BinaryFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#unaryTemporalFormula.
    def visitUnaryTemporalFormula(self, ctx:stlParser.UnaryTemporalFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by stlParser#unaryFormula.
    def visitUnaryFormula(self, ctx:stlParser.UnaryFormulaContext):
        return self.visitChildren(ctx)



del stlParser