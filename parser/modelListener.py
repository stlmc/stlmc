# Generated from model.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .modelParser import modelParser
else:
    from modelParser import modelParser

# This class defines a complete listener for a parse tree produced by modelParser.
class modelListener(ParseTreeListener):

    # Enter a parse tree produced by modelParser#stlMC.
    def enterStlMC(self, ctx:modelParser.StlMCContext):
        pass

    # Exit a parse tree produced by modelParser#stlMC.
    def exitStlMC(self, ctx:modelParser.StlMCContext):
        pass


    # Enter a parse tree produced by modelParser#expression.
    def enterExpression(self, ctx:modelParser.ExpressionContext):
        pass

    # Exit a parse tree produced by modelParser#expression.
    def exitExpression(self, ctx:modelParser.ExpressionContext):
        pass


    # Enter a parse tree produced by modelParser#condition.
    def enterCondition(self, ctx:modelParser.ConditionContext):
        pass

    # Exit a parse tree produced by modelParser#condition.
    def exitCondition(self, ctx:modelParser.ConditionContext):
        pass


    # Enter a parse tree produced by modelParser#diff_eq.
    def enterDiff_eq(self, ctx:modelParser.Diff_eqContext):
        pass

    # Exit a parse tree produced by modelParser#diff_eq.
    def exitDiff_eq(self, ctx:modelParser.Diff_eqContext):
        pass


    # Enter a parse tree produced by modelParser#sol_eq.
    def enterSol_eq(self, ctx:modelParser.Sol_eqContext):
        pass

    # Exit a parse tree produced by modelParser#sol_eq.
    def exitSol_eq(self, ctx:modelParser.Sol_eqContext):
        pass


    # Enter a parse tree produced by modelParser#mode_decl.
    def enterMode_decl(self, ctx:modelParser.Mode_declContext):
        pass

    # Exit a parse tree produced by modelParser#mode_decl.
    def exitMode_decl(self, ctx:modelParser.Mode_declContext):
        pass


    # Enter a parse tree produced by modelParser#inv_decl.
    def enterInv_decl(self, ctx:modelParser.Inv_declContext):
        pass

    # Exit a parse tree produced by modelParser#inv_decl.
    def exitInv_decl(self, ctx:modelParser.Inv_declContext):
        pass


    # Enter a parse tree produced by modelParser#flow_decl.
    def enterFlow_decl(self, ctx:modelParser.Flow_declContext):
        pass

    # Exit a parse tree produced by modelParser#flow_decl.
    def exitFlow_decl(self, ctx:modelParser.Flow_declContext):
        pass


    # Enter a parse tree produced by modelParser#jump_decl.
    def enterJump_decl(self, ctx:modelParser.Jump_declContext):
        pass

    # Exit a parse tree produced by modelParser#jump_decl.
    def exitJump_decl(self, ctx:modelParser.Jump_declContext):
        pass


    # Enter a parse tree produced by modelParser#mode_var_decl.
    def enterMode_var_decl(self, ctx:modelParser.Mode_var_declContext):
        pass

    # Exit a parse tree produced by modelParser#mode_var_decl.
    def exitMode_var_decl(self, ctx:modelParser.Mode_var_declContext):
        pass


    # Enter a parse tree produced by modelParser#variable_var_decl.
    def enterVariable_var_decl(self, ctx:modelParser.Variable_var_declContext):
        pass

    # Exit a parse tree produced by modelParser#variable_var_decl.
    def exitVariable_var_decl(self, ctx:modelParser.Variable_var_declContext):
        pass


    # Enter a parse tree produced by modelParser#mode_module.
    def enterMode_module(self, ctx:modelParser.Mode_moduleContext):
        pass

    # Exit a parse tree produced by modelParser#mode_module.
    def exitMode_module(self, ctx:modelParser.Mode_moduleContext):
        pass


    # Enter a parse tree produced by modelParser#init_decl.
    def enterInit_decl(self, ctx:modelParser.Init_declContext):
        pass

    # Exit a parse tree produced by modelParser#init_decl.
    def exitInit_decl(self, ctx:modelParser.Init_declContext):
        pass


    # Enter a parse tree produced by modelParser#goal_decl.
    def enterGoal_decl(self, ctx:modelParser.Goal_declContext):
        pass

    # Exit a parse tree produced by modelParser#goal_decl.
    def exitGoal_decl(self, ctx:modelParser.Goal_declContext):
        pass


    # Enter a parse tree produced by modelParser#leftEnd.
    def enterLeftEnd(self, ctx:modelParser.LeftEndContext):
        pass

    # Exit a parse tree produced by modelParser#leftEnd.
    def exitLeftEnd(self, ctx:modelParser.LeftEndContext):
        pass


    # Enter a parse tree produced by modelParser#rightEnd.
    def enterRightEnd(self, ctx:modelParser.RightEndContext):
        pass

    # Exit a parse tree produced by modelParser#rightEnd.
    def exitRightEnd(self, ctx:modelParser.RightEndContext):
        pass


    # Enter a parse tree produced by modelParser#interval.
    def enterInterval(self, ctx:modelParser.IntervalContext):
        pass

    # Exit a parse tree produced by modelParser#interval.
    def exitInterval(self, ctx:modelParser.IntervalContext):
        pass


    # Enter a parse tree produced by modelParser#parenFormula.
    def enterParenFormula(self, ctx:modelParser.ParenFormulaContext):
        pass

    # Exit a parse tree produced by modelParser#parenFormula.
    def exitParenFormula(self, ctx:modelParser.ParenFormulaContext):
        pass


    # Enter a parse tree produced by modelParser#constant.
    def enterConstant(self, ctx:modelParser.ConstantContext):
        pass

    # Exit a parse tree produced by modelParser#constant.
    def exitConstant(self, ctx:modelParser.ConstantContext):
        pass


    # Enter a parse tree produced by modelParser#binaryTemporalFormula.
    def enterBinaryTemporalFormula(self, ctx:modelParser.BinaryTemporalFormulaContext):
        pass

    # Exit a parse tree produced by modelParser#binaryTemporalFormula.
    def exitBinaryTemporalFormula(self, ctx:modelParser.BinaryTemporalFormulaContext):
        pass


    # Enter a parse tree produced by modelParser#proposition.
    def enterProposition(self, ctx:modelParser.PropositionContext):
        pass

    # Exit a parse tree produced by modelParser#proposition.
    def exitProposition(self, ctx:modelParser.PropositionContext):
        pass


    # Enter a parse tree produced by modelParser#binaryFormula.
    def enterBinaryFormula(self, ctx:modelParser.BinaryFormulaContext):
        pass

    # Exit a parse tree produced by modelParser#binaryFormula.
    def exitBinaryFormula(self, ctx:modelParser.BinaryFormulaContext):
        pass


    # Enter a parse tree produced by modelParser#unaryTemporalFormula.
    def enterUnaryTemporalFormula(self, ctx:modelParser.UnaryTemporalFormulaContext):
        pass

    # Exit a parse tree produced by modelParser#unaryTemporalFormula.
    def exitUnaryTemporalFormula(self, ctx:modelParser.UnaryTemporalFormulaContext):
        pass


    # Enter a parse tree produced by modelParser#unaryFormula.
    def enterUnaryFormula(self, ctx:modelParser.UnaryFormulaContext):
        pass

    # Exit a parse tree produced by modelParser#unaryFormula.
    def exitUnaryFormula(self, ctx:modelParser.UnaryFormulaContext):
        pass


