from antlr4 import *
from modelParser import modelParser
from modelVisitor import modelVisitor
from model import *
import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from stlMC import *
from core.formula import *

class modelVisitorImpl(modelVisitor):

    def __init__(self):
        pass

    '''
    stlMC
    '''
    def visitStlMC(self, ctx:modelParser.StlMCContext):
        modesDecl = list()
        varsDecl = list()
        modeModuleDecl = list()

        for i in range(len(ctx.mode_var_decl())):
            modesDecl.append(self.visit(ctx.mode_var_decl()[i]))

        for i in range(len(ctx.variable_var_decl())):
            varsDecl.append(self.visit(ctx.variable_var_decl()[i]))

        for i in range(len(ctx.mode_module())):
            modeModuleDecl.append(self.visit(ctx.mode_module()[i]))

        init = self.visit(ctx.init_decl())
 
        propDecl = list()
        for i in range(len(ctx.prop())):
            propDecl.append(self.visit(ctx.prop()[i]))
        goal = self.visit(ctx.goal_decl())

        return StlMC(modeDecl, varsDecl, modeModeleDecl, init, propDecl, goal) 


    '''
    mode_var_decl
    '''
    def visitMode_var_decl(self, ctx:modelParser.Mode_var_declContext):
        return Mode(ctx.var_type().getText(), ctx.VARIABLE().getText())

    '''
    variable_var_declaration
    '''
    def visitVariable_var_decl(self, ctx:modelParser.Variable_var_declContext):
        return ContVar(self.visit(ctx.var_range()), ctx.VARIABLE().getText())

    def visitBinaryExp(self, ctx:modelParser.BinaryExpContext):
        op = ctx.op.text
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        return BinaryExp(op, left, right)

    '''
    Not yet
    '''
    def visitUnaryExp(self, ctx:modelParser.UnaryExpContext):
        raise "Not yet in Unary Expression"

    def visitParenthesisExp(self, ctx:modelParser.ParenthesisExpContext):
        return self.visit(ctx.expression())

    def visitConstantExp(self, ctx:modelParser.ConstantExpContext):
        return ctx.VARIABLE().getText()

    def visitCompCond(self, ctx:modelParser.CompCondContext):
        op = ctx.op.text
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        return CompCond(op, left, right)

    def visitConstantCond(self, ctx:modelParser.ConstantCondContext):
        if ctx.TRUE():
            return BoolVal(True)
        elif ctx.FALSE() :
            return BoolVal(False)
        elif ctx.VARIABLE() :
            return ctx.VARIABLE().getText()

    def visitUnaryCond(self, ctx:modelParser.UnaryCondContext):
        return UnaryCond(ctx.op.text,self.visit(ctx.condition()))

    def visitMultiCond(self, ctx:modelParser.BinaryCondContext):
        prop = list()
        for i in range(len(ctx.condition())):
            prop.append(self.visit(ctx.condition()[i]))
        return BinaryCond(ctx.op.text, prop)

    def visitParenthesisCond(self, ctx:modelParser.ParenthesisCondContext):
        return self.visit(ctx.condition())

    '''
    jump redeclaration
    '''
    def visitParenthesisJump(self, ctx:modelParser.ParenthesisJumpContext):
        return self.visit(ctx.jump_redecl())

    def visitMultiJump(self, ctx:modelParser.MultiJumpContext):
        prop = list()
        for i in range(len(ctx.jump_redecl)):
            prop.append(self.visit(i))
        return MultiJump(ctx.op.text, prop) 

    def visitUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        return UnaryJump(ctx.op.text, self.visit(ctx.jump_redecl()))

    def visitBoolVar(self, ctx:modelParser.BoolVarContext):
        return NextVar(Bool(ctx.NEXT_VAR().getText()[:-1]))

    def visitJumpMod(self, ctx:modelParser.JumpModContext):
        return NextVar(self.contVar[ctx.NEXT_VAR().getText()]) == self.visit(ctx.expression())

    def vistVar_type(self, ctx:modelParser.Var_typeContext):
        return ctx.varType.text

    '''
    exact value variable
    '''
    def visitExactValue(self, ctx:modelParser.ExactValueContext):
        number = float(ctx.VALUE().getText())
        return (True, number, number, True) 

    '''
    variable range
    '''
    def visitVariableRange(self, ctx:modelParser.VariableRangeContext):
        leftBracket = True
        rightBracket = True 

        if ctx.leftParen.text == '(' :
            leftBracket = False

        if ctx.rightParen.text == ')' :
            rightBracket = False

        leftNumber = float(ctx.leftVal.text)
        rightNumber = float(ctx.rightVal.text)
        
        return (leftBracket, leftNumber,  rightNumber, rightBracket)

    '''
    flow differential equation type
    '''
    def visitDiff_Eq(self, ctx:modelParser.Diff_eqContext):
        return DiffEq(ctx.VARIABLE().getText(), self.visit(ctx.expression()))

    '''
    flow solution equation type
    '''
    def visitSol_Eq(self, ctx:modelParser.Sol_eqContext):
        return SolEq(ctx.VARIABLE()[0].getText(), self.visit(ctx.expression()))

    '''
    mode module
    '''
    def visitMode_module(self, ctx:modelParser.Mode_moduleContext):
        return modeModule(self.visit(ctx.mode_decl()), self.visit(ctx.inv_decl()), self.visit(ctx.flow_decl()), self.visit(ctx.jump_decl()))

    '''
    mode declaration
    '''
    def visitMode_decl(self, ctx:modelParser.Mode_declContext):
        element = list()
        for i in range(len(ctx.condition())):
            element.append(self.visit(ctx.condition()[i]))
        return MultiCond("and", element)
 
    '''
    invariant declaration
    '''
    def visitInv_decl(self, ctx:modelParser.Inv_declContext):
        element = list()
        for i in range(len(ctx.condition())):
            element.append(self.visit(ctx.condition()[i]))
        return MultiCond("and", element) 

    '''
    flow declaration
    '''
    def visitFlow_decl(self, ctx:modelParser.Flow_declContext):
        print("flow declaration")
        result = list()
        expType = "empty"
        if ctx.diff_eq():
           expType = "diff"
            for i in range(len(ctx.diff_eq())):
                result.append(self.visit(ctx.diff_eq()[i])) 
        elif ctx.sol_eq():
            expType = "sol"
            for i in range(len(ctx.sol_eq())):
                result.append(self.visit(ctx.sol_eq()[i]))

        return flowDecl(expType, result)

    '''
    jump declaration
    '''
    def visitJump_decl(self, ctx:modelParser.Jump_declContext):
        return jumpDecl(self.visit(ctx.condition()), self.visit(ctx.jump_redecl()))

    '''
    initial declaration
    '''
    def visitInit_decl(self, ctx:modelParser.Init_declContext):
        print("Init decl")
        return self.visit(ctx.condition())

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

    def visitProp(self, ctx:modelParser.PropContext):
        return propDecl(ctx.VARIABLE.getText(), self.visit(ctx.condition())) 

    '''
    goal declaration
    '''
    def visitGoal_decl(self, ctx:modelParser.Goal_declContext):
        print("Goal decl")
#        return self.visit(ctx.condition())
            

