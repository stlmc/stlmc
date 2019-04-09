from antlr4 import *
from core.syntax.modelParser import modelParser
from core.syntax.modelVisitor import modelVisitor
from core.model import *

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
        propDecl = list()
        self.newPropDecl = list()
        self.formulaText = list()

        for i in range(len(ctx.mode_var_decl())):
            modesDecl.append(self.visit(ctx.mode_var_decl()[i]))

        for i in range(len(ctx.variable_var_decl())):
            varsDecl.append(self.visit(ctx.variable_var_decl()[i]))

        for i in range(len(ctx.mode_module())):
            modeModuleDecl.append(self.visit(ctx.mode_module()[i]))

        init = self.visit(ctx.init_decl())

        if ctx.props():
            propDecl = self.visit(ctx.props())

        goal = self.visit(ctx.goal_decl())

        return StlMC(modesDecl, varsDecl, modeModuleDecl, init, (propDecl + self.newPropDecl), goal, self.formulaText) 

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
        if ctx.VARIABLE():
            return Real(ctx.VARIABLE().getText())
        elif ctx.VALUE():
            return RealVal(ctx.VALUE().getText())
        else:
            raise ("error in constant expression")

    def visitCompCond(self, ctx:modelParser.CompCondContext):
        op = ctx.op.text
        left = self.visit(ctx.condition()[0])
        right = self.visit(ctx.condition()[1])
        return CompCond(op, left, right)

    def visitCompExp(self, ctx:modelParser.CompExpContext):
        op = ctx.op.text
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        return CompCond(op, left, right)

    def visitConstantCond(self, ctx:modelParser.ConstantCondContext):
        if ctx.TRUE():
            return BoolVal(True)
        elif ctx.FALSE() :
            return BoolVal(False)
        elif ctx.VALUE():
            return RealVal(ctx.VALUE().getText())
        elif ctx.VARIABLE() :
            return ctx.VARIABLE().getText()
        else:
            raise ("error in constant condition")

    def visitUnaryCond(self, ctx:modelParser.UnaryCondContext):
        return UnaryCond(ctx.op.text,self.visit(ctx.condition()))

    def visitMultyCond(self, ctx:modelParser.MultyCondContext):
        prop = list()
        for i in range(len(ctx.condition())):
            prop.append(self.visit(ctx.condition()[i]))
        return MultyCond(ctx.op.text, prop)

    def visitParenthesisCond(self, ctx:modelParser.ParenthesisCondContext):
        return self.visit(ctx.condition())

    def visitBinaryCond(self, ctx:modelParser.BinaryCondContext):
        return BinaryCond(ctx.op.text, self.visit(ctx.condition()[0]), self.visit(ctx.condition()[1]))

    '''
    jump redeclaration
    '''
    def visitParenthesisJump(self, ctx:modelParser.ParenthesisJumpContext):
        return self.visit(ctx.jump_redecl())

    def visitMultyJump(self, ctx:modelParser.MultyJumpContext):
        prop = list()
        for i in range(len(ctx.jump_redecl())):
            prop.append(self.visit(ctx.jump_redecl()[i]))
        return MultyJump(ctx.op.text, prop) 

    def visitBinaryJump(self, ctx:modelParser.BinaryJumpContext):
        return BinaryJump(ctx.op.text, ctx.jump_redecl()[0], ctx.jump_redecl()[1])

    def visitUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        return UnaryJump(ctx.op.text, self.visit(ctx.jump_redecl()))

    def visitBoolVar(self, ctx:modelParser.BoolVarContext):
        return NextVar(Bool(ctx.NEXT_VAR().getText()[:-1]))

    def visitJumpMod(self, ctx:modelParser.JumpModContext):
        if ctx.TRUE():
            return jumpMod(ctx.NEXT_VAR().getText()[:-1], BoolVal(True))
        elif ctx.FALSE():
            return jumpMod(ctx.NEXT_VAR().getText()[:-1], BoolVal(False))
        else:
            return jumpMod(ctx.NEXT_VAR().getText()[:-1], self.visit(ctx.expression()))

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
    def visitDiff_eq(self, ctx:modelParser.Diff_eqContext):
        return DiffEq(ctx.VARIABLE().getText(), self.visit(ctx.expression()))

    '''
    flow solution equation type
    '''
    def visitSol_eq(self, ctx:modelParser.Sol_eqContext):
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
        return MultyCond("and", element)
 
    '''
    invariant declaration
    '''
    def visitInv_decl(self, ctx:modelParser.Inv_declContext):
        element = list()
        for i in range(len(ctx.condition())):
            element.append(self.visit(ctx.condition()[i]))
        return MultyCond("and", element) 

    '''
    flow declaration
    '''
    def visitFlow_decl(self, ctx:modelParser.Flow_declContext):
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
    def visitJump_redecl_module(self, ctx:modelParser.Jump_redecl_moduleContext):
        return jumpRedeclModule(self.visit(ctx.condition()), self.visit(ctx.jump_redecl())) 

    def visitJump_decl(self, ctx:modelParser.Jump_declContext):
        result = list()
        for i in range(len(ctx.jump_redecl_module())):
            result.append(self.visit(ctx.jump_redecl_module()[i]))
        return jumpDecl(result)

    '''
    initial declaration
    '''
    def visitInit_decl(self, ctx:modelParser.Init_declContext):
        return self.visit(ctx.condition())

    # Visit a parse tree produced by modelParser#leftEnd.
    def visitLeftEnd(self, ctx:modelParser.LeftEndContext):
        return (not ctx.LPAREN(), float(ctx.value.text))


    # Visit a parse tree produced by modelParser#rightEnd.
    def visitRightEnd(self, ctx:modelParser.RightEndContext):
        return (not ctx.RPAREN(), float(ctx.value.text))


    # Visit a parse tree produced by modelParser#interval.
    def visitInterval(self, ctx:modelParser.IntervalContext):
        if ctx.EQUAL():
            number = float(ctx.VALUE().getText())
            return Interval(True, number, True, number)
        else:
            left = self.visit(ctx.leftEnd())
            right = self.visit(ctx.rightEnd())
            return Interval(left[0], left[1], right[0], right[1])


    # Visit a parse tree produced by modelParser#parenFormula.
    def visitParenFormula(self, ctx:modelParser.ParenFormulaContext):
        return self.visit(ctx.formula())

    # Visit a parse tree produced by modelParser#proposition.
    def visitProposition(self, ctx:modelParser.PropositionContext):
        return PropositionFormula(ctx.VARIABLE().getText())

    # Visit a parse tree produced by modelParser#constant.
    def visitConstFormula(self, ctx:modelParser.ConstFormulaContext):
        return ConstantFormula(ctx.getText())

    def visitDirectCond(self, ctx:modelParser.DirectCondContext):
        newProp = "newPropDecl_" + str(len(self.newPropDecl))
 
        op = ctx.op.text
        if ctx.expression():
            left = self.visit(ctx.expression()[0])
            right = self.visit(ctx.expression()[1])
        else:
            left = self.visit(ctx.condition()[0])
            right = self.visit(ctx.condition()[1])
        self.newPropDecl.append(propDecl(newProp, CompCond(op, left, right))) 
        return PropositionFormula(newProp)

    # Visit a parse tree produced by modelParser#binaryFormula.
    def visitBinaryFormula(self, ctx:modelParser.BinaryFormulaContext):
        op = ctx.op.text
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        if op == '->':
            return ImpliesFormula(left,right)
        elif ((op == 'And') or (op == 'and')):
            return AndFormula([left,right])
        elif ((op == 'Or') or (op == 'or')):
            return OrFormula([left,right])
        else:
            raise "something wrong"

    def visitMultyFormula(self, ctx:modelParser.MultyFormulaContext):
        result = list()
        for i in range(len(ctx.formula())):
            result.append(self.visit(ctx.formula()[i]))
        return {'and' : AndFormula, 'or' : OrFormula, 'And' : AndFormula, 'Or' : OrFormula}[ctx.op.text](result)

    # Visit a parse tree produced by modelParser#unaryTemporalFormula.
    def visitUnaryTemporalFormula(self, ctx:modelParser.UnaryTemporalFormulaContext):
        time = self.visit(ctx.interval())
        child = self.visit(ctx.formula())
        return {'[]': GloballyFormula, '<>': FinallyFormula}[ctx.op.text](time, universeInterval, child)


    # Visit a parse tree produced by modelParser#unaryFormula.
    def visitUnaryFormula(self, ctx:modelParser.UnaryFormulaContext):
        child = self.visit(ctx.formula())
        return {'~': NotFormula}[ctx.op.text](child)

    def visitProps(self, ctx:modelParser.PropsContext):
        propDecl = list()
        for i in range(len(ctx.prop())):
            propDecl.append(self.visit(ctx.prop()[i]))

        return propDecl

    def visitProp(self, ctx:modelParser.PropContext):
        return propDecl(ctx.VARIABLE().getText(), self.visit(ctx.condition())) 

    '''
    goal declaration
    '''
    def visitGoal_decl(self, ctx:modelParser.Goal_declContext):
        formulaList = list()
        for i in range(len(ctx.formula())):
            self.formulaText.append(ctx.formula()[i].getText())
            formulaList.append(self.visit(ctx.formula()[i]))
        return formulaDecl(formulaList)

            

