# Generated from model.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .modelParser import modelParser
else:
    from modelParser import modelParser

# This class defines a complete generic visitor for a parse tree produced by modelParser.

class modelVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by modelParser#stlMC.
    def visitStlMC(self, ctx:modelParser.StlMCContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#mode_var_decl.
    def visitMode_var_decl(self, ctx:modelParser.Mode_var_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#variable_var_decl.
    def visitVariable_var_decl(self, ctx:modelParser.Variable_var_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#binaryExp.
    def visitBinaryExp(self, ctx:modelParser.BinaryExpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#unaryExp.
    def visitUnaryExp(self, ctx:modelParser.UnaryExpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#parenthesisExp.
    def visitParenthesisExp(self, ctx:modelParser.ParenthesisExpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#constantExp.
    def visitConstantExp(self, ctx:modelParser.ConstantExpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#constantCond.
    def visitConstantCond(self, ctx:modelParser.ConstantCondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#compCond.
    def visitCompCond(self, ctx:modelParser.CompCondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#unaryCond.
    def visitUnaryCond(self, ctx:modelParser.UnaryCondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#compExp.
    def visitCompExp(self, ctx:modelParser.CompExpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#multiCond.
    def visitMultiCond(self, ctx:modelParser.MultiCondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#parenthesisCond.
    def visitParenthesisCond(self, ctx:modelParser.ParenthesisCondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#parenthesisJump.
    def visitParenthesisJump(self, ctx:modelParser.ParenthesisJumpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#multiJump.
    def visitMultiJump(self, ctx:modelParser.MultiJumpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#unaryJump.
    def visitUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#boolVar.
    def visitBoolVar(self, ctx:modelParser.BoolVarContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#jumpMod.
    def visitJumpMod(self, ctx:modelParser.JumpModContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#var_type.
    def visitVar_type(self, ctx:modelParser.Var_typeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#exactValue.
    def visitExactValue(self, ctx:modelParser.ExactValueContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#variableRange.
    def visitVariableRange(self, ctx:modelParser.VariableRangeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#diff_eq.
    def visitDiff_eq(self, ctx:modelParser.Diff_eqContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#sol_eq.
    def visitSol_eq(self, ctx:modelParser.Sol_eqContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#mode_module.
    def visitMode_module(self, ctx:modelParser.Mode_moduleContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#mode_decl.
    def visitMode_decl(self, ctx:modelParser.Mode_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#inv_decl.
    def visitInv_decl(self, ctx:modelParser.Inv_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#flow_decl.
    def visitFlow_decl(self, ctx:modelParser.Flow_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#jump_redecl_module.
    def visitJump_redecl_module(self, ctx:modelParser.Jump_redecl_moduleContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#jump_decl.
    def visitJump_decl(self, ctx:modelParser.Jump_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#init_decl.
    def visitInit_decl(self, ctx:modelParser.Init_declContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#leftEnd.
    def visitLeftEnd(self, ctx:modelParser.LeftEndContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#rightEnd.
    def visitRightEnd(self, ctx:modelParser.RightEndContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#interval.
    def visitInterval(self, ctx:modelParser.IntervalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#parenFormula.
    def visitParenFormula(self, ctx:modelParser.ParenFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#constant.
    def visitConstant(self, ctx:modelParser.ConstantContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#directCond.
    def visitDirectCond(self, ctx:modelParser.DirectCondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#binaryTemporalFormula.
    def visitBinaryTemporalFormula(self, ctx:modelParser.BinaryTemporalFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#proposition.
    def visitProposition(self, ctx:modelParser.PropositionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#binaryFormula.
    def visitBinaryFormula(self, ctx:modelParser.BinaryFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#unaryTemporalFormula.
    def visitUnaryTemporalFormula(self, ctx:modelParser.UnaryTemporalFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#unaryFormula.
    def visitUnaryFormula(self, ctx:modelParser.UnaryFormulaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#prop.
    def visitProp(self, ctx:modelParser.PropContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by modelParser#goal_decl.
    def visitGoal_decl(self, ctx:modelParser.Goal_declContext):
        return self.visitChildren(ctx)



del modelParser