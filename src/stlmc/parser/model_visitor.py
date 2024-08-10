import sys
from typing import Dict

from antlr4 import FileStream, CommonTokenStream
from antlr4.error.ErrorListener import ErrorListener

from .error_listener import StlmcErrorListener
from ..constraints.constraints import *
from ..constraints.operations import substitution
from ..exception.exception import NotSupportedError
from ..objects.goal import ReachGoal
from ..objects.model import StlMC
from ..syntax.model.modelLexer import modelLexer
from ..syntax.model.modelParser import modelParser
from ..syntax.model.modelVisitor import modelVisitor


class ModelVisitor(modelVisitor):

    def __init__(self):
        self.type_context = dict()
        self.next_str = "##$%^&$%^&##'"
        self.range_dict = dict()
        self.constant_dict = dict()
        self.variable_declare_dict = dict()
        self.proposition_dict = dict()
        self.raw_proposition_dict = dict()
        self.goal_labels: Dict[Formula, str] = dict()
        self.temp_jump = None
        self.init_mode = None
        self.decl_ids = set()

    def get_parse_tree(self, file_name: str):
        raw_model = FileStream(file_name)
        lexer = modelLexer(raw_model)
        stream = CommonTokenStream(lexer)
        parser = modelParser(stream)
        parser.removeErrorListeners()
        model_err_listener = StlmcErrorListener()
        model_err_listener.name = file_name
        parser.addErrorListener(model_err_listener)
        tree = parser.stlMC()
        return self.visit(tree)

    '''
    stlMC
    '''

    def visitStlMC(self, ctx: modelParser.StlMCContext):
        module_declares = list()
        prop_declares = dict()

        # iterate through mode declaration
        for i in range(len(ctx.mode_var_decl())):
            self.visit(ctx.mode_var_decl()[i])

        for i in range(len(ctx.variable_var_decl())):
            self.visit(ctx.variable_var_decl()[i])

        for i in range(len(ctx.var_val_decl())):
            self.visit(ctx.var_val_decl()[i])

        self._update_decl_set()

        for i in range(len(ctx.mode_module())):
            module_declares.append(self.visit(ctx.mode_module()[i]))

        init = self.visit(ctx.init_decl())

        if ctx.props():
            self.raw_proposition_dict = self.visit(ctx.props())
            self.proposition_dict = self.raw_proposition_dict.copy()

        goals = self.visit(ctx.goal_decl())
        return StlMC(self.variable_declare_dict, self.range_dict, self.constant_dict, self.raw_proposition_dict,
                     module_declares, init, self.init_mode), self.proposition_dict, goals, self.goal_labels

    '''
    mode_var_decl
    '''

    def visitMode_var_decl(self, ctx: modelParser.Mode_var_declContext):
        op_dict = {'bool': Bool, 'real': Real, 'int': Int}
        name = ctx.VARIABLE().getText()
        v_type = ctx.var_type().getText()

        new_var = op_dict[v_type](name)
        if name in self.variable_declare_dict:
            return new_var
        else:
            self.variable_declare_dict[name] = new_var
            return new_var

    '''
    variable_var_declaration
    '''

    def visitVariable_var_decl(self, ctx: modelParser.Variable_var_declContext):
        new_var = Real(ctx.VARIABLE().getText())
        if new_var in self.range_dict:
            return new_var
        else:
            self.range_dict[new_var] = self.visit(ctx.var_range())
            return new_var

    '''
    variable_var_declaration
    '''

    def visitVar_val_decl(self, ctx: modelParser.Var_val_declContext):
        # return VarVal(ctx.var_type().getText(), ctx.VARIABLE().getText(), ctx.val.text)
        op_dict = {'bool': Bool, 'real': Real, 'int': Int}
        value_dict = {'bool': BoolVal, 'real': RealVal, 'int': IntVal}

        # infer type
        if ctx.val.text == "true" or ctx.val.text == "false":
            new_var = op_dict["bool"](ctx.VARIABLE().getText())
            new_val = value_dict["bool"](ctx.val.text)
        else:
            # try float conversion
            try:
                float(ctx.val.text)
            except ValueError:
                raise NotSupportedError("wrong value: {}".format(ctx.val.text))
            new_var = op_dict["real"](ctx.VARIABLE().getText())
            new_val = value_dict["real"](ctx.val.text)

        if new_var in self.constant_dict:
            raise NotSupportedError("{} is already declared".format(new_var))
        else:
            self.constant_dict[new_var] = new_val
            return new_var

    def _update_decl_set(self):
        self.decl_ids.update(self.variable_declare_dict.keys())
        for c in self.constant_dict:
            self.decl_ids.add(c.id)

        for r in self.range_dict:
            self.decl_ids.add(r.id)

    def visitBinaryExp(self, ctx: modelParser.BinaryExpContext):
        op_dict = {'+': Add, '-': Sub, '*': Mul, '/': Div, '**': Pow}
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        return op_dict[ctx.op.text](left, right)

    '''
    Not yet
    '''

    def visitUnaryExp(self, ctx: modelParser.UnaryExpContext):
        op = {"sin": Sin, "cos": Cos, "tan": Tan, "sqrt": Sqrt, "arcsin": Arcsin, "arccos": Arccos, "arctan": Arctan}
        if ctx.op.text in op.keys():
            return op[ctx.op.text](self.visit(ctx.expression()))
        elif ctx.op.text == "-":
            return Neg(self.visit(ctx.expression()))
        else:
            raise NotSupportedError("Can't support non-linear function")

    def visitParenthesisExp(self, ctx: modelParser.ParenthesisExpContext):
        return self.visit(ctx.expression())

    def visitConstantExp(self, ctx: modelParser.ConstantExpContext):
        if ctx.VARIABLE():
            if str(ctx.VARIABLE()) not in self.decl_ids:
                raise NotSupportedError("in the model file {}:{}, \'{}\' is not declared"
                                        .format(ctx.start.line, ctx.start.column, ctx.VARIABLE()))
            return Real(ctx.VARIABLE().getText())
        elif ctx.TIME():
            return Real('time')
        elif ctx.VALUE():
            return RealVal(ctx.VALUE().getText())
        else:
            raise NotSupportedError("error in constant expression")

    # TODO: New feature!
    def visitInitialValue(self, ctx: modelParser.InitialValueContext):
        return Real(ctx.INITIALVAL().getText()[0:-3])

    def visitCompCond(self, ctx: modelParser.CompCondContext):
        op_dict = {"=": Eq, "!=": Neq}
        left = self.visit(ctx.condition()[0])
        right = self.visit(ctx.condition()[1])
        if isinstance(left, Int):
            if "to" == left.id:
                assert isinstance(right, RealVal)
                self.init_mode = int(right.value)
                return BoolVal("True")
        return op_dict[ctx.op.text](left, right)

    def visitCompExp(self, ctx: modelParser.CompExpContext):
        op_dict = {'<=': Leq, '>=': Geq, "<": Lt, ">": Gt, "=": Eq, "!=": Neq}
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        return op_dict[ctx.op.text](left, right)

    def visitConstantCond(self, ctx: modelParser.ConstantCondContext):
        if ctx.TRUE():
            return BoolVal("True")
        elif ctx.FALSE():
            return BoolVal("False")
        elif ctx.VALUE():
            return RealVal(ctx.VALUE().getText())
        elif ctx.VARIABLE():
            var_text = ctx.VARIABLE().getText()
            guess_real_var = Real(var_text)
            guess_bool_var = Bool(var_text)
            if var_text in self.variable_declare_dict:
                return self.variable_declare_dict[var_text]
            elif guess_real_var in self.range_dict:
                return guess_real_var
            elif guess_bool_var in self.proposition_dict:
                return guess_bool_var
            else:
                raise NotSupportedError("in the model file {}:{}, \'{}\' is not declared"
                                        .format(ctx.start.line, ctx.start.column, ctx.VARIABLE()))
        raise NotSupportedError("error in constant condition")

    def visitUnaryCond(self, ctx: modelParser.UnaryCondContext):
        return Not(self.visit(ctx.condition()))

    def visitMultyCond(self, ctx: modelParser.MultyCondContext):
        op_dict = {'and': And, 'or': Or}
        prop = list()
        for i in range(len(ctx.condition())):
            prop.append(self.visit(ctx.condition()[i]))
        return op_dict[ctx.op.text](prop)

    def visitParenthesisCond(self, ctx: modelParser.ParenthesisCondContext):
        return self.visit(ctx.condition())

    '''
    jump redeclaration
    '''

    def visitParenthesisJump(self, ctx: modelParser.ParenthesisJumpContext):
        return self.visit(ctx.jump_redecl())

    def visitMultyJump(self, ctx: modelParser.MultyJumpContext):
        op_dict = {'and': And, 'or': Or}
        prop = list()
        for i in range(len(ctx.jump_redecl())):
            prop.append(self.visit(ctx.jump_redecl()[i]))
        return op_dict[ctx.op.text](prop)

    def visitUnaryJump(self, ctx: modelParser.UnaryJumpContext):
        return Not(self.visit(ctx.jump_redecl()))

    def visitBoolVar(self, ctx: modelParser.BoolVarContext):
        return Bool(ctx.NEXT_VAR().getText()[:-1] + self.next_str)

    def visitJumpMod(self, ctx: modelParser.JumpModContext):
        if ctx.TRUE():
            return Eq(Bool(ctx.NEXT_VAR().getText()[:-1] + self.next_str), BoolVal("True"))
        elif ctx.FALSE():
            return Eq(Bool(ctx.NEXT_VAR().getText()[:-1] + self.next_str), BoolVal("False"))
        else:
            op_dict = {'<=': Leq, '>=': Geq, "<": Lt, ">": Gt, "=": Eq, "!=": Neq}
            v_id = ctx.NEXT_VAR().getText()[:-1]
            # guess
            guess_var = Real(ctx.NEXT_VAR().getText()[:-1])
            guess_var_bool = Bool(ctx.NEXT_VAR().getText()[:-1])
            guess_var_int = Int(ctx.NEXT_VAR().getText()[:-1])

            if "to" == v_id:
                j = self.visit(ctx.expression())
                assert isinstance(j, RealVal)
                self.temp_jump = int(j.value)
                return BoolVal("True")

            real_var = Real(ctx.NEXT_VAR().getText()[:-1] + self.next_str)
            bool_var = Bool(ctx.NEXT_VAR().getText()[:-1] + self.next_str)
            int_var = Int(ctx.NEXT_VAR().getText()[:-1] + self.next_str)
            if guess_var in self.range_dict:
                return op_dict[ctx.op.text](real_var, self.visit(ctx.expression()))
            elif guess_var_bool in self.variable_declare_dict:
                return op_dict[ctx.op.text](bool_var, self.visit(ctx.expression()))
            elif guess_var_int in self.variable_declare_dict:
                return op_dict[ctx.op.text](int_var, self.visit(ctx.expression()))
            elif guess_var in self.variable_declare_dict:
                return op_dict[ctx.op.text](real_var, self.visit(ctx.expression()))
            else:
                if v_id not in self.decl_ids:
                    raise NotSupportedError("in the model file {}:{}, \'{}\' is not declared"
                                            .format(ctx.start.line, ctx.start.column, v_id))
                raise NotSupportedError("Cannot visit jump mod")

    def visitVar_type(self, ctx: modelParser.Var_typeContext):
        return ctx.varType.text

    '''
    exact value variable
    '''

    def visitExactValue(self, ctx: modelParser.ExactValueContext):
        number = float(ctx.VALUE().getText())
        return True, number, number, True

    '''
    variable range
    '''

    def visitVariableRange(self, ctx: modelParser.VariableRangeContext):
        left_bracket = True
        right_bracket = True

        if ctx.leftParen.text == '(':
            left_bracket = False

        if ctx.rightParen.text == ')':
            right_bracket = False

        left_number = float(ctx.leftVal.text)
        right_number = float(ctx.rightVal.text)

        return left_bracket, left_number, right_number, right_bracket

    '''
    flow differential equation type
    '''

    def visitDiff_eq(self, ctx: modelParser.Diff_eqContext):
        return Real(ctx.VARIABLE().getText()), self.visit(ctx.expression())

    '''
    flow solution equation type
    '''

    def visitSol_eq(self, ctx: modelParser.Sol_eqContext):
        return Real(ctx.VARIABLE().getText()), self.visit(ctx.expression())

    '''
    mode module
    '''

    def visitMode_module(self, ctx: modelParser.Mode_moduleContext):
        mode_dict = dict()
        mode_dict["mode"] = self.visit(ctx.mode_decl())
        mode_dict["flow"] = self.visit(ctx.flow_decl())
        mode_dict["inv"] = self.visit(ctx.inv_decl())
        mode_dict["jump"], mode_dict["jp_d"] = self.visit(ctx.jump_decl())
        return mode_dict

    '''
    mode declaration
    '''

    def visitMode_decl(self, ctx: modelParser.Mode_declContext):
        element = list()
        for i in range(len(ctx.condition())):
            # CompCond type
            element.append(self.visit(ctx.condition()[i]))
        return And(element)

    '''
    invariant declaration
    '''

    def visitInv_decl(self, ctx: modelParser.Inv_declContext):
        element = list()
        for i in range(len(ctx.condition())):
            element.append(self.visit(ctx.condition()[i]))
        return And(element)

    '''
    flow declaration
    '''

    def visitFlow_decl(self, ctx: modelParser.Flow_declContext):
        vars = list()
        exps = list()
        if ctx.diff_eq():
            for i in range(len(ctx.diff_eq())):
                var, exp = self.visit(ctx.diff_eq()[i])
                vars.append(var)
                exps.append(exp)
            vars = [substitution(v, self.constant_dict) for v in vars]
            exps = [substitution(e, self.constant_dict) for e in exps]
            return Ode(vars, exps)
        elif ctx.sol_eq():
            for i in range(len(ctx.sol_eq())):
                var, exp = self.visit(ctx.sol_eq()[i])
                vars.append(var)
                exps.append(exp)
            vars = [substitution(v, self.constant_dict) for v in vars]
            exps = [substitution(e, self.constant_dict) for e in exps]
            return Function(vars, exps)

    '''
    jump declaration
    '''

    def visitJump_redecl_module(self, ctx: modelParser.Jump_redecl_moduleContext):
        return self.visit(ctx.condition()), self.visit(ctx.jump_redecl())

    def visitJump_decl(self, ctx: modelParser.Jump_declContext):
        result = dict()
        jp_id_d = dict()
        for i in range(len(ctx.jump_redecl_module())):
            assert self.temp_jump is None
            cond, jump = self.visit(ctx.jump_redecl_module()[i])
            result[cond] = jump
            if self.temp_jump is not None:
                jp_id_d[cond] = self.temp_jump
                self.temp_jump = None
        return result, jp_id_d

    '''
    initial declaration
    '''

    def visitInit_decl(self, ctx: modelParser.Init_declContext):
        # return self.visit(ctx.condition())
        cond = list()
        for i in range(len(ctx.condition())):
            # CompCond type
            cond.append(self.visit(ctx.condition()[i]))
        return And(cond)

    # Visit a parse tree produced by modelParser#leftEnd.
    def visitLeftEnd(self, ctx: modelParser.LeftEndContext):
        return not ctx.LPAREN(), float(ctx.value.text)

    # Visit a parse tree produced by modelParser#rightEnd.
    def visitRightEnd(self, ctx: modelParser.RightEndContext):
        return not ctx.RPAREN(), float(ctx.value.text)

    # Visit a parse tree produced by modelParser#interval.
    def visitInterval(self, ctx: modelParser.IntervalContext):
        if ctx.EQUAL():
            number = RealVal(ctx.VALUE().getText())
            return Interval(True, number, True, number)
        else:
            left = self.visit(ctx.leftEnd())
            right = self.visit(ctx.rightEnd())
            return Interval(left[0], RealVal(str(left[1])), right[0], RealVal(str(right[1])))

    # Visit a parse tree produced by modelParser#parenFormula.
    def visitParenFormula(self, ctx: modelParser.ParenFormulaContext):
        return self.visit(ctx.formula())

    # Visit a parse tree produced by modelParser#proposition.
    def visitProposition(self, ctx: modelParser.PropositionContext):
        return Bool(ctx.VARIABLE().getText())

    # Visit a parse tree produced by modelParser#constant.
    def visitConstFormula(self, ctx: modelParser.ConstFormulaContext):
        return BoolVal(ctx.getText())

    # TODO : Problem
    def visitDirectCond(self, ctx: modelParser.DirectCondContext):
        new_var_str = "newPropDecl_" + str(len(self.proposition_dict))
        new_var = Bool(new_var_str)
        op_dict = {'<=': Leq, '>=': Geq, "<": Lt, ">": Gt, "=": Eq, "!=": Neq}
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        self.proposition_dict[new_var] = op_dict[ctx.op.text](left, right)
        return new_var

    # Visit a parse tree produced by modelParser#binaryFormula.
    def visitBinaryFormula(self, ctx: modelParser.BinaryFormulaContext):
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        op = ctx.op.text
        if op == '->':
            return Implies(left, right)
        elif op == 'and':
            return And([left, right])
        elif op == 'or':
            return Or([left, right])
        else:
            raise NotSupportedError("something wrong")

    def visitMultyFormula(self, ctx: modelParser.MultyFormulaContext):
        result = list()
        for i in range(len(ctx.formula())):
            result.append(self.visit(ctx.formula()[i]))
        return {'and': And, 'or': Or, 'And': And, 'Or': Or}[ctx.op.text](result)

    # Visit a parse tree produced by modelParser#unaryTemporalFormula.
    def visitUnaryTemporalFormula(self, ctx: modelParser.UnaryTemporalFormulaContext):
        time = self.visit(ctx.interval())
        child = self.visit(ctx.formula())
        return {'[]': GloballyFormula, '<>': FinallyFormula}[ctx.op.text](time, universeInterval, child)

    # Visit a parse tree produced by stlParser#binaryTemporalFormula.
    def visitBinaryTemporalFormula(self, ctx: modelParser.BinaryTemporalFormulaContext):
        time = self.visit(ctx.interval())
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        return {'U': UntilFormula, 'R': ReleaseFormula}[ctx.op.text](time, universeInterval, left, right)

    # Visit a parse tree produced by modelParser#unaryFormula.
    def visitUnaryFormula(self, ctx: modelParser.UnaryFormulaContext):
        child = self.visit(ctx.formula())
        return {'~': Not}[ctx.op.text](child)

    def visitProps(self, ctx: modelParser.PropsContext):
        proposition_mapping_dict = dict()
        for i in range(len(ctx.prop())):
            prop_var, prop_cond = self.visit(ctx.prop()[i])
            proposition_mapping_dict[prop_var] = prop_cond
        return proposition_mapping_dict

    def visitProp(self, ctx: modelParser.PropContext):
        return Bool(ctx.VARIABLE().getText()), self.visit(ctx.condition())

    # Visit a parse tree produced by modelParser#labeledStlGoal.
    def visitLabeledStlGoal(self, ctx: modelParser.LabeledStlGoalContext):
        return self.visit(ctx.formula()), ctx.VARIABLE().getText(), False

    # Visit a parse tree produced by modelParser#unlabeledStlGoal.
    def visitUnlabeledStlGoal(self, ctx: modelParser.UnlabeledStlGoalContext):
        return self.visit(ctx.formula()), None, False

    # Visit a parse tree produced by modelParser#reachGoal.
    def visitReachGoal(self, ctx: modelParser.ReachGoalContext):
        return self.visit(ctx.condition()), None, True

    def visitGoal_decl(self, ctx: modelParser.Goal_declContext):
        labeled_goals = list()
        unlabeled_goals = list()
        reach_goals = list()
        for i in range(len(ctx.goal_unit())):
            goal, label, is_reach = self.visit(ctx.goal_unit()[i])
            if label is None:
                if is_reach:
                    reach_goals.append(goal)
                else:
                    unlabeled_goals.append(goal)
            else:
                labeled_goals.append(goal)
                self.goal_labels[goal] = label
            # type of formula
        return labeled_goals, unlabeled_goals, reach_goals
