from antlr4 import *
from modelParser import modelParser
from modelVisitor import modelVisitor
from .stlMC import *
from .core.constraint import *

class modelVisitorImpl(modelVisitor):
    '''
    Expression 
    '''
    def visitParenExp(self, ctx:modelParser.ParenthesisExpContext):
        return self.visit(ctx.formula())

    def visitBinaryExp(self, ctx:modelParser.BinaryExpContext):
        op = ctx.op.text
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        if op == '+':
            return Plus(left,right)
        elif op == '-':
            return Minus(left,right)
        elif op == '*':
            return Mul(left,right)
        elif op == '/':
            return Div(left,right)
        else:
            raise "something wrong"

    def visitUnaryExp(self, ctx:modelParser.UnaryExpContext):
        return DefFunction(ctx.getText())

    def visitConstantExp(self, ctx:modelParser.ConstantExpContext):
        if ctx.VARIABLE():
           id = ctx.getText()



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
        return self.visit(ctx.formula())

    def visitCompCond(self, ctx:modelParser.CompCondContext):
        op = ctx.op.text
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        if op == '<':
            return Lt(left,right)
        elif op == '<=':
            return Le(left,right)
        elif op == '>':
            return Gt(left,right)
        elif op == '>=':
            return Ge(left,right)
        elif op == '==':
            return Numeq(left,right)
        elif op == '!=':
            return Numneq(left,right)
        else:
            raise "something wrong"

    def visitBinaryCond(self, ctx:modelParser.BinaryCondContext):
        op = ctx.op.text
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        if op == 'and':
            return And([left,right])
        elif op == 'or':
            return Or([left,right])
        else:
            raise "something wrong"

    def visitUnaryCond(self, ctx:modelParser.UnaryCondContext):
        return Not(ctx.getText())
         
    def visitConstantCond(self, ctx:modelParser.ConstantCondContext):
        if ctx.TRUE():
            return BoolVal(True) 
        elif ctx.FALSE() :
            return BoolVal(False) 
        elif ctx.VARIABLE() :
           id = ctx.getText()


        else:
            raise "something wrong"

    '''
    jump redeclaration
    '''
    def visitParenJump(self, ctx:modelParser.ParenthesisJumpContext):
        return self.visit(ctx.formula())

    def visitBinaryJump(self, ctx:modelParser.BinaryJumpContext):
        op = ctx.op.text
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        if op == 'and':
            return And([left,right])
        elif op == 'or':
            return Or([left,right])
        else:
            raise "something wrong"

    def visitUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        return Not(ctx.getText())

    def visitCondMod(self, ctx:modelParser.ConditionModText):
        return (ctx.getText())

    def visitJumpMod(self, ctx:modelParser.JumpModContext):
        next_state = self.visit(ctx.jump_redecl_module())
        return NextDef(next_state)


    '''
    jump_redeclaration modulde
    '''
    def visitJumpRedeclMod(self, ctx:modelParser.Jump_redecl_moduleContext):
        return Numeq(NextVar(ctx.NEXT_VAR().text), ctx.expression().getText()) 

    '''
    flow differential equation type
    '''
    def visitDiffEq(self, ctx:modelParser.Diff_eqContext):
        return 




    '''
    mode_var_decl
    '''
    def visitModeVarDecl(self, ctx:modelParser.Mode_var_declContext):
        if ctx.BOOL():
            return Bool(ctx.VARIABLE().text)
        elif ctx.INT():
            return Int(ctx.VARIABLE().text)
        elif ctx.REAL():
            return Real(ctx.VARIABLE().text)
        else:
            raise "something wrong"


    '''
    variable_var_declaration
    '''
    def visitVariableVarDecl(self, ctx:modelParser.Variable_var_declContext):
        if ~ctx.EQUAL():
            left = self.visit(ctx.leftEnd())
            right = self.visit(ctx.rightEnd())
            if lef 
            return And(self.VARIABLE().text > left, self.VARIABLE().text < right)


 
