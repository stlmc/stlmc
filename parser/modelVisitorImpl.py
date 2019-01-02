from antlr4 import *
from modelParser import modelParser
from modelVisitor import modelVisitor
import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from stlMC import *

class modelVisitorImpl(modelVisitor):

    def __init__(self):
        self.resultMode = dict()
        self.resultFlow = dict()
        self.resultInv = dict()
        self.resultJump = dict()


    # Visit a parse tree produced by modelParser#leftEnd.
    def visitLeftEnd(self, ctx:modelParser.LeftEndContext):
        return (not ctx.LPAREN(), float(ctx.value.text))


    # Visit a parse tree produced by modelParser#rightEnd.
    def visitRightEnd(self, ctx:modelParser.RightEndContext):
        return (not ctx.RPAREN(), float(ctx.value.text))

    '''
    Expression 
    '''
    def visitParenExp(self, ctx:modelParser.ParenthesisExpContext):
        return self.visit(ctx.expression())

    def visitBinaryExp(self, ctx:modelParser.BinaryExpContext):
        op = ctx.op.text
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        if op == '+':
            return self.visit(left) + self.visit(right)
        elif op == '-':
            return self.visit(left) - self.visit(right)
        elif op == '*':
            return self.visit(left) * self.visit(right)
        elif op == '/':
            return self.visit(left) / self.visit(right)
        else:
            raise "something wrong"
   

    '''
    Not yet
    '''
    def visitUnaryExp(self, ctx:modelParser.UnaryExpContext):
        pass


    def visitConstantExp(self, ctx:modelParser.ConstantExpContext):
        if ctx.VARIABLE():
            id = ctx.getText()
            return id
        elif ctx.INT_NUM() :
            return IntVal(ctx.getText())
        elif ctx.REAL_NUM() :
            return RealVal(ctx.getText())
        else:
            raise "something wrong"

    '''
    Condition
    '''
    def visitParenCond(self, ctx:modelParser.ParenthesisCondContext):
        return self.visit(ctx.condition())

    def visitCompCond(self, ctx:modelParser.CompCondContext):
        op = ctx.op.text
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        if op == '<':
            return left < right
        elif op == '<=':
            return left <= right
        elif op == '>':
            return left > right
        elif op == '>=':
            return left >= right
        elif op == '==':
            return left == right
        elif op == '!=':
            return left != right
        else:
            raise "something wrong"

    def visitBinaryCond(self, ctx:modelParser.BinaryCondContext):
        op = ctx.op.text
        left = self.visit(ctx.condition()[0])
        right = self.visit(ctx.condition()[1])
        if op == 'and':
            return And(left,right)
        elif op == 'or':
            return Or(left,right)
        else:
            raise "something wrong"

    def visitUnaryCond(self, ctx:modelParser.UnaryCondContext):
        return Not(self.visit(ctx.condition()))
         
    def visitConstantCond(self, ctx:modelParser.ConstantCondContext):
        if ctx.TRUE():
            return BoolVal(True) 
        elif ctx.FALSE() :
            return BoolVal(False) 
        elif ctx.VARIABLE() :
            id = ctx.getText()
            return id
        else:
            raise "something wrong"

    '''
    jump redeclaration
    '''
    def visitParenJump(self, ctx:modelParser.ParenthesisJumpContext):
        return self.visit(ctx.jump_redecl())

    def visitBinaryJump(self, ctx:modelParser.BinaryJumpContext):
        op = ctx.op.text
        left = self.visit(ctx.jump_redecl()[0])
        right = self.visit(ctx.jump_redecl()[1])
        if op == 'and':
            return And(left,right)
        elif op == 'or':
            return Or(left,right)
        else:
            raise "something wrong"

    def visitUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        return Not(self.visit(ctx.jump_redecl()))

    def visitConditionMod(self, ctx:modelParser.ConditionModContext):
        return self.visit(ctx.condition())

    def visitJumpMod(self, ctx:modelParser.JumpModContext):
        return NextVar(ctx.NEXT_VAR().getText()) == self.visit(ctx.expression())

    '''
    flow differential equation type
    '''
    def visitDiffEq(self, ctx:modelParser.Diff_eqContext):
        result = dict()
        result[ctx.VARIABLE().getText()] = self.visit(ctx.expression())
        return result

    '''
    flow solution equation type
    '''
    def visitSolEq(self, ctx:modelParser.Sol_eqContext):
        result = dict()
        result[ctx.VARIABLE()[0].getText()] = self.visit(ctx.expression())
        return result

    '''
    mode declaration
    '''
    def visitModeDecl(self, ctx:modelParser.Mode_declContext):
        return And(*self.visit(ctx.condition()))
 
    '''
    invariant declaration
    '''
    def visitInvDecl(self, ctx:modelParser.Inv_declContext):
        return And(*self.visit(ctx.condition()))

    '''
    flow declaration
    '''
    def visitFlowDecl(self, ctx:modelParser.Flow_declContext):
        resultDict = dict()
        if ctx.diff_eq():
            for i in range(len(ctx.diff_eq())):
                resultDict.update(self.visit(ctx.diff_eq()[i])) 
            return resultDict
        elif ctx.sol_eq():
            for i in range(len(ctx.sol_eq())):
                resultDict.update(self.visit(ctx.sol_eq()[i]))
            return resultDict
        else:
            raise "something wrong"

    '''
    jump declaration
    '''
    def visitJumpDecl(self, ctx:modelParser.Jump_declContext):
        result = dict()
        result[self.visit(ctx.condition())] = self.visit(ctx.jump_redecl())
        return result


    '''
    mode_var_decl
    '''
    def visitModeVarDecl(self, ctx:modelParser.Mode_var_declContext):
        if ctx.BOOL():
             self.resultMode[ctx.VARIABLE().getText()] = Bool 
        elif ctx.INT():
             self.resultMode[ctx.VARIABLE().getText()] = Int
        elif ctx.REAL():
             self.resultMode[ctx.VARIABLE().getText()] = Real
        else:
            raise "something wrong"


    '''
    variable_var_declaration
    '''
    def visitVariableVarDecl(self, ctx:modelParser.Variable_var_declContext):
        resultInterval = dict()
        if ctx.EQUAL():
            resultInterval[self.VARIABLE().getText()] = (float(ctx.NUMVER().getText()), float(ctx.NUMVER().getText()))
        else:
            left = self.visit(ctx.leftEnd())
            right = self.visit(ctx.rightEnd())
            resultInterval[self.VARIABLE().getText()] = (left[1], right[1]) # true include equal, if left[0] is true equal
        return resultInterval
  
    '''
    mode module
    '''
    def visitModeModule(self, ctx:modelParser.Mode_moduleContext):
        modeCond = self.visit(ctx.mode_decl())
        self.resultFlow[modeCond] = self.visit(ctx.flow_decl())
        self.resultInv[modeCond] = self.visit(ctx.inv_decl())
        self.resultJump = self.visit(ctx.jump_decl())

    '''
    initial declaration
    '''
    def visitInitDecl(self, ctx:modelParser.Init_declContext):
        return self.visit(ctx.condition())


    '''
    goal declaration
    '''
    def visitGoalDecl(self, ctx:modelParser.Goal_declContext):
        return self.visit(ctx.condition())
            
    
    '''
    stlMC
    '''
    def visitStlMC(self, ctx:modelParser.StlMCContext):
        resultVar = dict()
        for i in range(len(ctx.variable_var_decl())):
            resultVar.update(self.visit(ctx.variable_var_decl()[i])) 
#        return Model(self.resultMode, resultVar, self.visit(ctx.init_decl()), self.resultFlow, self.resultInv, self.resultJump) 
        print(self.resultMode)
        print(resultVar)
        print(self.visit(ctx.init_decl()))
        print(self.resultFlow)
        print(self.resultInv)
        print(self.resultJump) 
 
