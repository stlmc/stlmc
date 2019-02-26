from antlr4 import *
from modelParser import modelParser
from modelVisitor import modelVisitor
import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from stlMC import *

class modelVisitorImpl(modelVisitor):

    def __init__(self):
        self.modeVar = dict()
        self.contVar = dict()

    '''
    Expression 
    '''
    def visitParenthesisExp(self, ctx:modelParser.ParenthesisExpContext):
        print("paren")
        return self.visit(ctx.expression())

    def visitBinaryExp(self, ctx:modelParser.BinaryExpContext):
        print("Binary exp")
        op = ctx.op.text
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        if op == '+':
            return left + right
        elif op == '-':
            return left - right
        elif op == '*':
            return left * right
        elif op == '/':
            return left / right
        else:
            raise "something wrong"
   

    '''
    Not yet
    '''
    def visitUnaryExp(self, ctx:modelParser.UnaryExpContext):
        print("Unary exp")
        pass


    def visitConstantExp(self, ctx:modelParser.ConstantExpContext):
        print("Const exp")
        if ctx.VALUE():
            return Real(ctx.VALUE().getText())
        elif ctx.TRUE():
            return BoolVal(True)
        elif ctx.FALSE():
            return BoolVal(False)
        elif ctx.VARIABLE():
            if ctx.VARIABLE().getText() in self.contVar.keys():
                return self.contVar[ctx.VARIABLE().getText()] 
            else:
                return self.modeVar[ctx.VARIABLE().getText()]
        else:
            pass
    '''
    Condition
    '''
    def visitParenthesisCond(self, ctx:modelParser.ParenthesisCondContext):
        print("paren condition")
        return self.visit(ctx.condition())

    def visitCompCond(self, ctx:modelParser.CompCondContext):
        print("Compare condition")
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
        print("Binary condition")
        prop = list()
        for i in range(len(ctx.condition())):
            prop.append(self.visit(ctx.condition()[i]))
        return {'and' : And, 'or' : Or}[ctx.op.text](*prop)

    def visitUnaryCond(self, ctx:modelParser.UnaryCondContext):
        print("Unary condition")
        return Not(self.visit(ctx.condition()))

    def visitConstantCond(self, ctx:modelParser.ConstantCondContext):
        print("Constant condition")
        if ctx.TRUE():
            return BoolVal(True) 
        elif ctx.FALSE() :
            return BoolVal(False) 
        elif ctx.VARIABLE() :
            if ctx.VARIABLE().getText() in self.modeVar.keys():
                return self.modeVar[ctx.VARIABLE().getText()]
            else:
                return self.contVar[ctx.VARIABLE().getText()] 
        else:
            raise "something wrong"

    '''
    jump redeclaration
    '''
    def visitParenthesisJump(self, ctx:modelParser.ParenthesisJumpContext):
        print("Paren jump")
        return self.visit(ctx.jump_redecl())

    def visitMultiJump(self, ctx:modelParser.MultiJumpContext):
        print("Binary jump")
        prop = list()
        for i in range(len(ctx.jump_redecl)):
            prop.append(self.visit(i))
        op = ctx.op.text
        return {'and' : And, 'or' : Or}[ctx.op.text](*prop)

    def visitUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        print("Unary jump")
        return Not(self.visit(ctx.jump_redecl()))

    def visitJumpMod(self, ctx:modelParser.JumpModContext):
        print("jump module")
        return NextVar(self.contVar[ctx.NEXT_VAR().getText()]) == self.visit(ctx.expression())

    def visitBoolVar(self, ctx:modelParser.BoolVarContext):
        print("Next variable boolean")
        return NextVar(Bool(ctx.NEXT_VAR().getText()[:-1]))

    '''
    flow differential equation type
    '''
    def visitDiff_Eq(self, ctx:modelParser.Diff_eqContext):
        print("differential equation")
        result = dict()
        result[self.contVar[ctx.VARIABLE().getText()]] = self.visit(ctx.expression())
        return result

    '''
    flow solution equation type
    '''
    def visitSol_Eq(self, ctx:modelParser.Sol_eqContext):
        print("Solution equation")
        result = dict()
        result[self.contVar[ctx.VARIABLE()[0].getText()]] = self.visit(ctx.expression())
        return result

    '''
    mode declaration
    '''
    def visitMode_decl(self, ctx:modelParser.Mode_declContext):
        print("mode declaration")
        element = list()
        for i in range(len(ctx.condition())):
            element.append(self.visit(ctx.condition()[i]))
        return And(*element)
 
    '''
    invariant declaration
    '''
    def visitInv_decl(self, ctx:modelParser.Inv_declContext):
        print("invariant declaration")
        element = list()
        for i in range(len(ctx.condition())):
            element.append(self.visit(ctx.condition()[i]))
        return And(*element)

    '''
    flow declaration
    '''
    def visitFlow_decl(self, ctx:modelParser.Flow_declContext):
        print("flow declaration")
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
    def visitJump_decl(self, ctx:modelParser.Jump_declContext):
        print("jump declaration")
        result = dict()
        result[self.visit(ctx.condition())] = self.visit(ctx.jump_redecl())
        return result


    '''
    mode_var_decl
    '''
    def visitMode_var_decl(self, ctx:modelParser.Mode_var_declContext):
        return {ctx.VARIABLE().getText() : {'bool' : Bool, 'int' : Int, 'real' : Real}[ctx.var_type().getText()](ctx.VARIABLE().getText())}

    '''
    exact value variable
    '''
    def visitExactValue(self, ctx:modelParser.ExactValueContext):
        return [ctx.VALUE().getText(), ctx.VALUE().getText()]

    '''
    variable range
    '''
    def visitVariableRange(self, ctx:modelParser.VariableRangeContext):
        '''
        if ctx.leftParen.text == '(' :
            if ctx.rightParen.text == ')' :
                return I.open(float(ctx.leftVal.text), float(ctx.rightVal.text))
            else:
                return I.openclosed(float(ctx.leftVal.text), float(ctx.rightVal.text))
        else:
            if ctx.rightParen.text == ')' :
                return I.closedopen(float(ctx.leftVal.text), float(ctx.rightVal.text))
            else :
                return [float(ctx.leftVal.text), float(ctx.rightVal.text)]
        '''
        return ctx.leftParen.text + ctx.leftVal.text + "," +  ctx.rightVal.text + ctx.rightParen.text
 

    '''
    variable_var_declaration
    '''
    def visitVariable_var_decl(self, ctx:modelParser.Variable_var_declContext):
        return {ctx.VARIABLE().getText() : self.visit(ctx.var_range())}
  
    '''
    mode module
    '''
    def visitMode_module(self, ctx:modelParser.Mode_moduleContext):
        print("Mode mulde decl")
        inv = dict()
        flow = dict()
        jump = dict()

        modeCond = self.visit(ctx.mode_decl())
        inv[modeCond] = self.visit(ctx.inv_decl())
        flow[modeCond] = self.visit(ctx.flow_decl())
        jump[modeCond] = self.visit(ctx.jump_decl())         
        
        return(inv, flow, jump)

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
            
    def dictAppend(origin, append):
        for k in append.keys():
            origin[k] = append[k]
        return origin

    '''
    stlMC
    '''
    def visitStlMC(self, ctx:modelParser.StlMCContext):
        flow = dict()
        inv = dict()
        jump = dict()

        prop = dict()


             
        for i in range(len(ctx.mode_var_decl())):
            self.modeVar.update(self.visit(ctx.mode_var_decl()[i]))


        for i in range(len(ctx.variable_var_decl())):
            appendDict = self.visit(ctx.variable_var_decl()[i])
            self.contVar.update(appendDict)

        for i in range(len(ctx.mode_module())):
            (invEle, flowEle, jumpEle) = self.visit(ctx.mode_module()[i])
            inv = self.dictAppend(inv, invEle)
            flow = self.dictAppend(flow, flowEle)
            jump = self.dictAppend(jump, jumpEle)

#        init = self.visit(ctx.init_decl())
#        goal = self.visit(ctx.goal_decl())

#        return Model(self.contVar, init, flow, inv, jump, prop)

