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


    # Enter a parse tree produced by modelParser#binaryExp.
    def enterBinaryExp(self, ctx:modelParser.BinaryExpContext):
        pass

    # Exit a parse tree produced by modelParser#binaryExp.
    def exitBinaryExp(self, ctx:modelParser.BinaryExpContext):
        pass


    # Enter a parse tree produced by modelParser#unaryExp.
    def enterUnaryExp(self, ctx:modelParser.UnaryExpContext):
        pass

    # Exit a parse tree produced by modelParser#unaryExp.
    def exitUnaryExp(self, ctx:modelParser.UnaryExpContext):
        pass


    # Enter a parse tree produced by modelParser#parenthesisExp.
    def enterParenthesisExp(self, ctx:modelParser.ParenthesisExpContext):
        pass

    # Exit a parse tree produced by modelParser#parenthesisExp.
    def exitParenthesisExp(self, ctx:modelParser.ParenthesisExpContext):
        pass


    # Enter a parse tree produced by modelParser#constantExp.
    def enterConstantExp(self, ctx:modelParser.ConstantExpContext):
        pass

    # Exit a parse tree produced by modelParser#constantExp.
    def exitConstantExp(self, ctx:modelParser.ConstantExpContext):
        pass


    # Enter a parse tree produced by modelParser#parenthesisCond.
    def enterParenthesisCond(self, ctx:modelParser.ParenthesisCondContext):
        pass

    # Exit a parse tree produced by modelParser#parenthesisCond.
    def exitParenthesisCond(self, ctx:modelParser.ParenthesisCondContext):
        pass


    # Enter a parse tree produced by modelParser#compCond.
    def enterCompCond(self, ctx:modelParser.CompCondContext):
        pass

    # Exit a parse tree produced by modelParser#compCond.
    def exitCompCond(self, ctx:modelParser.CompCondContext):
        pass


    # Enter a parse tree produced by modelParser#binaryCond.
    def enterBinaryCond(self, ctx:modelParser.BinaryCondContext):
        pass

    # Exit a parse tree produced by modelParser#binaryCond.
    def exitBinaryCond(self, ctx:modelParser.BinaryCondContext):
        pass


    # Enter a parse tree produced by modelParser#unaryCond.
    def enterUnaryCond(self, ctx:modelParser.UnaryCondContext):
        pass

    # Exit a parse tree produced by modelParser#unaryCond.
    def exitUnaryCond(self, ctx:modelParser.UnaryCondContext):
        pass


    # Enter a parse tree produced by modelParser#constantCond.
    def enterConstantCond(self, ctx:modelParser.ConstantCondContext):
        pass

    # Exit a parse tree produced by modelParser#constantCond.
    def exitConstantCond(self, ctx:modelParser.ConstantCondContext):
        pass


    # Enter a parse tree produced by modelParser#parenthesisJump.
    def enterParenthesisJump(self, ctx:modelParser.ParenthesisJumpContext):
        pass

    # Exit a parse tree produced by modelParser#parenthesisJump.
    def exitParenthesisJump(self, ctx:modelParser.ParenthesisJumpContext):
        pass


    # Enter a parse tree produced by modelParser#binaryJump.
    def enterBinaryJump(self, ctx:modelParser.BinaryJumpContext):
        pass

    # Exit a parse tree produced by modelParser#binaryJump.
    def exitBinaryJump(self, ctx:modelParser.BinaryJumpContext):
        pass


    # Enter a parse tree produced by modelParser#unaryJump.
    def enterUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        pass

    # Exit a parse tree produced by modelParser#unaryJump.
    def exitUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        pass


    # Enter a parse tree produced by modelParser#conditionMod.
    def enterConditionMod(self, ctx:modelParser.ConditionModContext):
        pass

    # Exit a parse tree produced by modelParser#conditionMod.
    def exitConditionMod(self, ctx:modelParser.ConditionModContext):
        pass


    # Enter a parse tree produced by modelParser#jumpMod.
    def enterJumpMod(self, ctx:modelParser.JumpModContext):
        pass

    # Exit a parse tree produced by modelParser#jumpMod.
    def exitJumpMod(self, ctx:modelParser.JumpModContext):
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


