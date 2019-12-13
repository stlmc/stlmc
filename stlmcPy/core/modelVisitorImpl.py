from antlr4 import *
from stlmcPy.core.syntax.modelParser import modelParser
from stlmcPy.core.syntax.modelVisitor import modelVisitor
from stlmcPy.core.model import *

class VisitorException(Exception):
    def __init__(self, expression, message):
        print("Exception occured : " + str(type(expression)))
        print("=======> " + message)

class modelVisitorImpl(modelVisitor):

    def __init__(self):
        pass

    '''
    stlMC
    '''
    def visitStlMC(self, ctx:modelParser.StlMCContext):
        modesDecl = list()
        varsDecl = list()
        varvalDict = dict()
        modeModuleDecl = list()
        propDecl = list()
        self.newPropDecl = list()
        self.formulaText = list()
        self.var_dic = list()
        # check if model file contains
        self.isTri = False

        # generate variable dictionary * number of mode module
        for i in range(len(ctx.mode_module())):
            dic = dict()
            dic["time"] = 0.0
            self.var_dic.append(dic)

        # iterate through mode declaration
        for i in range(len(ctx.mode_var_decl())):
            md = self.visitMode_var_decl(ctx.mode_var_decl()[i])
            modesDecl.append(md)
            # set every instance with none
            for j in range(len(ctx.mode_module())):
                self.var_dic[j][md.id] = None

        for i in range(len(ctx.variable_var_decl())):
            vs = self.visitVariable_var_decl(ctx.variable_var_decl()[i])
            varsDecl.append(vs)
            for j in range(len(ctx.mode_module())):
                self.var_dic[j][vs.id] = None

        for i in range(len(ctx.var_val_decl())):
            element = self.visitVar_val_decl(ctx.var_val_decl()[i])
            (elemid, elemval) = element.getElement() 
            varvalDict[str(elemid)] = elemval


        for i in range(len(ctx.mode_module())):
            modeModuleDecl.append(self.visitMode_module(ctx.mode_module()[i], self.var_dic[i]))

        init = self.visit(ctx.init_decl())

        if ctx.props():
            propDecl = self.visit(ctx.props())

        goal = self.visit(ctx.goal_decl())


        return (StlMC(modesDecl, varsDecl, varvalDict, modeModuleDecl, init, (propDecl + self.newPropDecl), goal, self.formulaText), self.isTri)

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

    '''
    variable_var_declaration
    '''
    def visitVar_val_decl(self, ctx:modelParser.Var_val_declContext):
        return VarVal(ctx.var_type().getText(), ctx.VARIABLE().getText(), ctx.val.text)

    def visitBinaryExp(self, ctx:modelParser.BinaryExpContext, var_dic=dict()):
        left = None
        right = None
        op = ctx.op.text
        # var_dic is empty
        if not var_dic:
            left = self.visit(ctx.expression()[0])
            right = self.visit(ctx.expression()[1])
        else:
            left = self.visitExpression(ctx.expression()[0], var_dic)
            right = self.visitExpression(ctx.expression()[1], var_dic)
        return BinaryExp(op, left, right)

    '''
    Not yet
    '''
    def visitUnaryExp(self, ctx:modelParser.UnaryExpContext, var_dic=dict()):
        if ctx.op.text in ['sin', 'cos', 'tan', 'log', 'sqrt']:
            self.isTri = True
            #raise ("Can't support non-linear function")
        return UnaryFunc(ctx.op.text, self.visitExpression(ctx.expression(), var_dic), var_dic)

    def visitParenthesisExp(self, ctx:modelParser.ParenthesisExpContext, var_dict=dict()):
        if not var_dict:
            return self.visit(ctx.expression())
        else:
            return self.visitExpression(ctx.expression(), var_dict)

    def visitConstantExp(self, ctx:modelParser.ConstantExpContext, var_dict=dict()):
        if ctx.VARIABLE():
            r = Real(ctx.VARIABLE().getText())
            r.var_dic = var_dict
            return r
        elif ctx.TIME():
            r = Real('time')
            r.var_dic = var_dict
            return r
        elif ctx.VALUE():
            return RealVal(ctx.VALUE().getText())
        else:
            raise ("error in constant expression")

    # TODO: New feature!
    def visitInitialValue(self, ctx:modelParser.InitialValueContext, var_dict=dict()):
        r = InitVal(ctx.INITIALVAL().getText())
        r.var_dic = var_dict
        return r

    def visitCompCond(self, ctx:modelParser.CompCondContext, var_dict=dict()):
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
        left = self.visit(ctx.jump_redecl()[0])
        right = self.visit(ctx.jump_redecl()[1])
        return BinaryJump(ctx.op.text, left, right)

    def visitUnaryJump(self, ctx:modelParser.UnaryJumpContext):
        return UnaryJump(ctx.op.text, self.visit(ctx.jump_redecl()))

    def visitBoolVar(self, ctx:modelParser.BoolVarContext):
        return NextVar(Bool(ctx.NEXT_VAR().getText()[:-1]))

    def visitJumpMod(self, ctx:modelParser.JumpModContext):
        if ctx.TRUE():
            return jumpMod(ctx.op.text, ctx.NEXT_VAR().getText()[:-1], BoolVal(True))
        elif ctx.FALSE():
            return jumpMod(ctx.op.text, ctx.NEXT_VAR().getText()[:-1], BoolVal(False))
        else:
            return jumpMod(ctx.op.text, ctx.NEXT_VAR().getText()[:-1], self.visit(ctx.expression()))

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

    # new function for expression
    def visitExpression(self, ctx:modelParser.ExpressionContext, var_dict=dict()):
        # empty
        if not var_dict:
            return self.visit(ctx)
        else:
            if isinstance(ctx, modelParser.InitialValueContext):
                return self.visitInitialValue(ctx)
            elif isinstance(ctx, modelParser.ConstantExpContext):
                return self.visitConstantExp(ctx, var_dict)
            elif isinstance(ctx, modelParser.BinaryExpContext):
                return self.visitBinaryExp(ctx, var_dict)
            elif isinstance(ctx, modelParser.ParenthesisExpContext):
                return self.visitParenthesisExp(ctx, var_dict)
            elif isinstance(ctx, modelParser.UnaryExpContext):
                return self.visitUnaryExp(ctx, var_dict)


    '''
    flow differential equation type
    '''
    def visitDiff_eq(self, ctx:modelParser.Diff_eqContext, var_dict=dict()):
        return DiffEq(ctx.VARIABLE().getText(), self.visitExpression(ctx.expression(), var_dict))

    '''
    flow solution equation type
    '''
    def visitSol_eq(self, ctx:modelParser.Sol_eqContext, var_dict=dict()):
        return SolEq(ctx.VARIABLE().getText(), self.visitExpression(ctx.expression(), var_dict))

    '''
    mode module
    '''
    def visitMode_module(self, ctx:modelParser.Mode_moduleContext, var_dic):
        return modeModule(self.visitMode_decl(ctx.mode_decl()), self.visit(ctx.inv_decl()), self.visitFlow_decl(ctx.flow_decl(), var_dic), self.visit(ctx.jump_decl()))

    '''
    mode declaration
    '''
    def visitMode_decl(self, ctx:modelParser.Mode_declContext):
        element = list()
        for i in range(len(ctx.condition())):
            # CompCond type
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
    def visitFlow_decl(self, ctx:modelParser.Flow_declContext, var_dic):
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

        v_list = []
        f_result = []
        if ctx.diff_eq():
            for e in result:
                # get var ID
                v_list.append(e.contVar)

        elif ctx.sol_eq():
            for e in result:
                v_list.append(e.contVar)

        # time only have one variable, time.
        # time_dict is single value not dict.
        for e in v_list:
            var_dic[e]=0.0

        var_dic["time"]=0.0

        if ctx.diff_eq():
            expType = "diff"
            # check if there exist variable
            for i in range(len(ctx.diff_eq())):
                a = self.visitDiff_eq(ctx.diff_eq()[i], var_dic)
                f_result.append(a)
        elif ctx.sol_eq():
            expType = "sol"
            # testing....
            for i in range(len(ctx.sol_eq())):
                 f_result.append(self.visitSol_eq(ctx.sol_eq()[i], var_dic))
        return flowDecl(expType, f_result, var_dic)

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

        self.newPropDecl.append(propDecl(newProp, self.visit(ctx.condition())))
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

    # Visit a parse tree produced by stlParser#binaryTemporalFormula.
    def visitBinaryTemporalFormula(self, ctx:modelParser.BinaryTemporalFormulaContext):
       time = self.visit(ctx.interval())
       left = self.visit(ctx.formula()[0])
       right = self.visit(ctx.formula()[1])
       return {'U': UntilFormula, 'R': ReleaseFormula}[ctx.op.text](time, universeInterval, left, right)

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



