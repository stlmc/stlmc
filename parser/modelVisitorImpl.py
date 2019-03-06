from antlr4 import *
from modelParser import modelParser
from modelVisitor import modelVisitor
from model import *
import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from stlMC import *

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
        goal = self.visit(ctx.goal_decl())

        return StlMC(modeDecl, varsDecl, modeModeleDecl, init, goal) 


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

    def visitParenthesisCond(self, ctx:modelParser.ParenthesisCondContext):
        return self.visit(ctx.condition())

    def visitCompCond(self, ctx:modelParser.CompCondContext):
        op = ctx.op.text
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        return CompCond(op, left, right)

    def visitMultiCond(self, ctx:modelParser.BinaryCondContext):
        prop = list()
        for i in range(len(ctx.condition())):
            prop.append(self.visit(ctx.condition()[i]))
        return BinaryCond(ctx.op.text, prop)

    def visitUnaryCond(self, ctx:modelParser.UnaryCondContext):
        return UnaryCond(ctx.op.text,self.visit(ctx.condition()))

    def visitConstantCond(self, ctx:modelParser.ConstantCondContext):
        if ctx.TRUE():
            return BoolVal(True) 
        elif ctx.FALSE() :
            return BoolVal(False) 
        elif ctx.VARIABLE() :
            return ctx.VARIABLE().getText()

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


    '''
    goal declaration
    '''
    def visitGoal_decl(self, ctx:modelParser.Goal_declContext):
        print("Goal decl")
#        return self.visit(ctx.condition())
            

