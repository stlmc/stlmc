from typing import Dict, Tuple

from antlr4 import InputStream, FileStream, CommonTokenStream
from .model_parser import ModelParser
from .error_listener import StlmcErrorListener
from ..constraints.aux.generator import *
from ..constraints.constraints import *
from ..exception.exception import NotSupportedError
from ..syntax.model.modelLexer import modelLexer
from ..syntax.model.modelParser import modelParser
from ..syntax.model.modelVisitor import modelVisitor


class StlmcParser(ModelParser, modelVisitor):

    def __init__(self):
        self.type_context = dict()
        self.next_str = "$next"

        # variable declarations
        self.variable_decls = VariableDeclaration()

        # range info
        self.range_info: Dict[Real, Interval] = dict()
        # constant info
        self.constant_info = dict()

        self.proposition_dict = dict()
        self.goal_labels: Dict[Formula, str] = dict()
        self.temp_jump = None
        self.init_mode = None

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
    

    def parse_goals(self, file_name: str):
        # ignore declaration checking
        self.variable_decls.ignore = True
        raw_model = InputStream(file_name)
        lexer = modelLexer(raw_model)
        stream = CommonTokenStream(lexer)
        parser = modelParser(stream)
        parser.removeErrorListeners()
        model_err_listener = StlmcErrorListener()
        parser.addErrorListener(model_err_listener)
        tree = parser.stlGoals()
        res = self.visit(tree)
        self.variable_decls.ignore = False
        return res

    '''
    stlMC
    '''

    def visitStlMC(self, ctx: modelParser.StlMCContext):
        module_declares = list()

        # iterate mode variables
        for i in range(len(ctx.mode_var_decl())):
            self.visit(ctx.mode_var_decl()[i])

        # continuous
        for i in range(len(ctx.variable_var_decl())):
            self.visit(ctx.variable_var_decl()[i])

        # constant
        for i in range(len(ctx.var_val_decl())):
            self.visit(ctx.var_val_decl()[i])

        self.variable_decls.unique_checking()

        for i in range(len(ctx.mode_module())):
            module_declares.append(self.visit(ctx.mode_module()[i]))

        init = self.visit(ctx.init_decl())

        if ctx.props():
            self.proposition_dict = self.visit(ctx.props())

        goals = self.visit(ctx.goal_decl())
        # print(self.range_info)
        # print(self.proposition_dict)
        # print(self.constant_info)
        variable_decl = self.variable_decls.get_declaration()
        # print(module_declares)
        # print(init)
        return (module_declares, init, self.next_str, variable_decl, self.range_info, self.constant_info,
                self.proposition_dict, self.init_mode), self.proposition_dict, goals, self.goal_labels
    
    
    # Visit a parse tree produced by modelParser#stlGoals.
    def visitStlGoals(self, ctx:modelParser.StlGoalsContext):
        labeled_goals = dict()
        unlabeled_goals = list()
        reach_goals = list()

        for i in range(len(ctx.goal_unit())):
            goal, label, is_reach = self.visit(ctx.goal_unit(i))
            if label is None:
                if is_reach:
                    reach_goals.append(goal)
                else:
                    unlabeled_goals.append(goal)
            else:
                labeled_goals[label] = goal

        return labeled_goals, unlabeled_goals, reach_goals


    '''
    declaration of mode variables
    '''

    def visitMode_var_decl(self, ctx: modelParser.Mode_var_declContext):
        name = str(ctx.VARIABLE().getText())
        ty = str(ctx.var_type().getText())

        if self.variable_decls.is_declared(name):
            raise NotSupportedError("{} is already declared".format(name))

        self.variable_decls.declare(name, ty, "mode")
        return variable(name, ty)

    '''
    declaration of continuous variables
    '''

    def visitVariable_var_decl(self, ctx: modelParser.Variable_var_declContext):
        name, ty = str(ctx.VARIABLE().getText()), "real"
        v = variable(name, ty)

        if self.variable_decls.is_declared(name):
            raise NotSupportedError("{} is already declared".format(name))
        self.variable_decls.declare(name, ty, "continuous")
        self.range_info[v] = self.visit(ctx.var_range())

        return v

    '''
    declaration of constant variables
    '''

    def visitVar_val_decl(self, ctx: modelParser.Var_val_declContext):
        name = str(ctx.VARIABLE().getText())
        val_str = str(ctx.val.text).lower()

        if self.variable_decls.is_declared(name):
            raise NotSupportedError("{} is already declared".format(name))

        # infer type
        if val_str == "true" or val_str == "false":
            val, ty = val_str.capitalize(), "bool"
        else:
            # try float conversion
            try:
                float(val_str)
            except ValueError:
                raise NotSupportedError("wrong value: {}".format(val_str))
            val, ty = val_str, "real"

        v, val = variable(name, ty), value(val, ty)
        self.variable_decls.declare(name, ty, "constant")
        self.constant_info[v] = val
        return v

    def visitBinaryExp(self, ctx: modelParser.BinaryExpContext):
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        op_str = str(ctx.op.text)
        return binary_expr(left, right, op_str)

    '''
    Not yet
    '''

    def visitUnaryExp(self, ctx: modelParser.UnaryExpContext):
        op_str = str(ctx.op.text).lower()
        if op_str == "-":
            return Neg(self.visit(ctx.expression()))
        else:
            unary_exp = unary_expr(self.visit(ctx.expression()), op_str)
            if unary_exp is None:
                raise NotSupportedError("Can't support non-linear function")
            return unary_exp

    def visitParenthesisExp(self, ctx: modelParser.ParenthesisExpContext):
        return self.visit(ctx.expression())

    def visitConstantExp(self, ctx: modelParser.ConstantExpContext):
        if ctx.VARIABLE():
            name = str(ctx.VARIABLE())
            if not self.variable_decls.is_declared(name):
                raise NotSupportedError("in the model file {}:{}, \'{}\' is not declared"
                                        .format(ctx.start.line, ctx.start.column, ctx.VARIABLE()))
            return variable(name, "real")
        elif ctx.TIME():
            return variable("time", "real")
        elif ctx.VALUE():
            val = str(ctx.VALUE().getText())
            return value(val, "real")
        else:
            raise NotSupportedError("error in constant expression")

    def visitInitialValue(self, ctx: modelParser.InitialValueContext):
        initial_name = str(ctx.INITIALVAL().getText())
        name = initial_name[0:-3]
        return variable(name, "real")

    def visitCompCond(self, ctx: modelParser.CompCondContext):
        # op_dict = {"=": Eq, "!=": Neq}
        left = self.visit(ctx.condition()[0])
        right = self.visit(ctx.condition()[1])
        op_str = str(ctx.op.text)

        # reach
        if isinstance(left, Int):
            if "to" == left.id:
                assert isinstance(right, RealVal)
                self.init_mode = int(right.value)
                return BoolVal("True")
        return binary_formula(left, right, op_str)

    def visitCompExp(self, ctx: modelParser.CompExpContext):
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        op_str = str(ctx.op.text)
        return binary_proposition(left, right, op_str)

    def visitConstantCond(self, ctx: modelParser.ConstantCondContext):
        if ctx.TRUE():
            return value("True", "bool")
        elif ctx.FALSE():
            return value("False", "bool")
        elif ctx.VALUE():
            val = str(ctx.VALUE().getText())
            return value(val, "real")
        elif ctx.VARIABLE():
            name = str(ctx.VARIABLE().getText())

            if not self.variable_decls.is_declared(name):
                raise NotSupportedError("in the model file {}:{}, \'{}\' is not declared"
                                        .format(ctx.start.line, ctx.start.column, name))

            ty = self.variable_decls.get_type(name)
            return variable(name, ty)
        else:
            raise NotSupportedError("error in constant condition")

    def visitUnaryCond(self, ctx: modelParser.UnaryCondContext):
        return Not(self.visit(ctx.condition()))

    def visitMultyCond(self, ctx: modelParser.MultyCondContext):
        children = list()
        for i in range(len(ctx.condition())):
            children.append(self.visit(ctx.condition()[i]))
        op_str = str(ctx.op.text)
        return multinary_formula(children, op_str)

    def visitParenthesisCond(self, ctx: modelParser.ParenthesisCondContext):
        return self.visit(ctx.condition())

    '''
    jump redeclaration
    '''

    def visitParenthesisJump(self, ctx: modelParser.ParenthesisJumpContext):
        return self.visit(ctx.jump_redecl())

    def visitMultyJump(self, ctx: modelParser.MultyJumpContext):
        children = list()
        for i in range(len(ctx.jump_redecl())):
            children.append(self.visit(ctx.jump_redecl()[i]))
        op_str = str(ctx.op.text)
        return multinary_formula(children, op_str)

    def visitUnaryJump(self, ctx: modelParser.UnaryJumpContext):
        return Not(self.visit(ctx.jump_redecl()))

    def visitBoolVar(self, ctx: modelParser.BoolVarContext):
        return Bool(ctx.NEXT_VAR().getText()[:-1] + self.next_str)

    def visitJumpMod(self, ctx: modelParser.JumpModContext):
        primed_name = str(ctx.NEXT_VAR().getText())
        name = primed_name[:-1]
        new_primed_name = "{}{}".format(name, self.next_str)
        if ctx.TRUE():
            return Bool(new_primed_name) == BoolVal("True")
        elif ctx.FALSE():
            return Bool(new_primed_name) == BoolVal("False")
        else:
            if not self.variable_decls.is_declared(name):
                raise NotSupportedError("in the model file {}:{}, \'{}\' is not declared"
                                        .format(ctx.start.line, ctx.start.column, name))

            ty = self.variable_decls.get_type(name)

            if "to" == name:
                j = self.visit(ctx.expression())
                assert isinstance(j, RealVal)
                self.temp_jump = int(j.value)
                return BoolVal("True")

            left = variable(new_primed_name, ty)
            right = self.visit(ctx.expression())
            op_str = str(ctx.op.text)
            return binary_proposition(left, right, op_str)

    def visitVar_type(self, ctx: modelParser.Var_typeContext):
        return ctx.varType.text

    '''
    exact value variable
    '''

    def visitExactValue(self, ctx: modelParser.ExactValueContext):
        number = value(str(ctx.VALUE().getText()), "real")
        return Interval(True, number, number, True)

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

        left_number = value(str(ctx.leftVal.text), "real")
        right_number = value(str(ctx.rightVal.text), "real")

        return Interval(left_bracket, left_number, right_number, right_bracket)

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
        return element

    '''
    invariant declaration
    '''

    def visitInv_decl(self, ctx: modelParser.Inv_declContext):
        element = list()
        for i in range(len(ctx.condition())):
            element.append(self.visit(ctx.condition()[i]))
        return element

    '''
    flow declaration
    '''

    def visitFlow_decl(self, ctx: modelParser.Flow_declContext):
        vs = list()
        exps = list()
        if ctx.diff_eq():
            for i in range(len(ctx.diff_eq())):
                v, exp = self.visit(ctx.diff_eq()[i])
                vs.append(v)
                exps.append(exp)
            return Ode(vs, exps)
        elif ctx.sol_eq():
            for i in range(len(ctx.sol_eq())):
                v, exp = self.visit(ctx.sol_eq()[i])
                vs.append(v)
                exps.append(exp)
            return Function(vs, exps)

    '''
    jump declaration
    '''

    def visitJump_redecl_module(self, ctx: modelParser.Jump_redecl_moduleContext):
        return self.visit(ctx.condition()), self.visit(ctx.jump_redecl())

    def visitJump_decl(self, ctx: modelParser.Jump_declContext):
        result = list()
        jp_id_d = dict()
        for jp in ctx.jump_redecl_module():
            assert self.temp_jump is None
            pre_jp, post_jp = self.visit(jp)
            result.append((pre_jp, post_jp))
            if self.temp_jump is not None:
                jp_id_d[pre_jp] = self.temp_jump
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
        return cond

    # Visit a parse tree produced by modelParser#leftEnd.
    def visitLeftEnd(self, ctx: modelParser.LeftEndContext):
        return not ctx.LPAREN(), float(ctx.value.text)

    # Visit a parse tree produced by modelParser#rightEnd.
    def visitRightEnd(self, ctx: modelParser.RightEndContext):
        return not ctx.RPAREN(), float(ctx.value.text)

    # Visit a parse tree produced by modelParser#interval.
    def visitInterval(self, ctx: modelParser.IntervalContext):
        if ctx.EQUAL():
            val = str(ctx.VALUE().getText())
            number = value(val, "real")
            return Interval(True, number, number, True)
        else:
            left = self.visit(ctx.leftEnd())
            right = self.visit(ctx.rightEnd())
            return Interval(left[0], RealVal(str(left[1])), RealVal(str(right[1])), right[0])

    # Visit a parse tree produced by modelParser#parenFormula.
    def visitParenFormula(self, ctx: modelParser.ParenFormulaContext):
        return self.visit(ctx.formula())

    # Visit a parse tree produced by modelParser#proposition.
    def visitProposition(self, ctx: modelParser.PropositionContext):
        return Bool(str(ctx.VARIABLE().getText()))

    # Visit a parse tree produced by modelParser#constant.
    def visitConstFormula(self, ctx: modelParser.ConstFormulaContext):
        return BoolVal(str(ctx.getText()))

    def visitDirectCond(self, ctx: modelParser.DirectCondContext):
        left = self.visit(ctx.expression()[0])
        right = self.visit(ctx.expression()[1])
        op_str = str(ctx.op.text)
        return binary_proposition(left, right, op_str)

    # Visit a parse tree produced by modelParser#binaryFormula.
    def visitBinaryFormula(self, ctx: modelParser.BinaryFormulaContext):
        left = self.visit(ctx.formula()[0])
        right = self.visit(ctx.formula()[1])
        op_str = str(ctx.op.text)
        if op_str == '->':
            return Implies(left, right)
        else:
            f = multinary_formula([left, right], op_str)
            if f is None:
                raise NotSupportedError("{} is not a valid type".format(op_str))
            return f

    def visitMultyFormula(self, ctx: modelParser.MultyFormulaContext):
        result = list()
        for i in range(len(ctx.formula())):
            result.append(self.visit(ctx.formula()[i]))
        op_str = str(ctx.op.text).lower()
        return multinary_formula(result, op_str)

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


class VariableDeclaration:
    def __init__(self):
        self._v_decls = dict()
        self._v_decls["mode"] = set()
        self._v_decls["continuous"] = set()
        self._v_decls["constant"] = set()
        self.ignore = False

    def declare(self, v_name: str, v_ty: str, ty: str):
        if self.is_declared(v_name):
            return

        is_mode = ty == "mode"
        is_cont = ty == "continuous"
        is_const = ty == "constant"

        if is_mode:
            self._v_decls["mode"].add(variable(v_name, v_ty))
        elif is_cont:
            self._v_decls["continuous"].add(variable(v_name, v_ty))
        elif is_const:
            self._v_decls["constant"].add(variable(v_name, v_ty))
        else:
            raise NotSupportedError("invalid type {}".format(ty))

    def is_declared(self, name: str) -> bool:
        if self.ignore:
            return True

        is_int, is_real, is_bool = self._is_declared(name)
        return is_int or is_real or is_bool

    def _is_declared(self, name: str) -> Tuple[bool, bool, bool]:
        mo_decl = self._v_decls["mode"]
        cs_decl = self._v_decls["continuous"]
        ct_decl = self._v_decls["constant"]

        guess_int = variable(name, "int")
        guess_real = variable(name, "real")
        guess_bool = variable(name, "bool")

        is_int = guess_int in mo_decl or guess_int in cs_decl or guess_int in ct_decl
        is_real = guess_real in mo_decl or guess_real in cs_decl or guess_real in ct_decl
        is_bool = guess_bool in mo_decl or guess_bool in cs_decl or guess_bool in ct_decl

        return is_int, is_real, is_bool

    def get_type(self, name: str) -> str:
        is_int, is_real, is_bool = self._is_declared(name)

        if is_int:
            return "int"
        elif is_real:
            return "real"
        elif is_bool:
            return "bool"
        else:
            raise NotSupportedError("{} does not declared".format(name))

    def get_declaration(self):
        return self._v_decls

    def unique_checking(self):
        mo_decl = self._v_decls["mode"]
        cs_decl = self._v_decls["continuous"]
        ct_decl = self._v_decls["constant"]

        # check if there are the same variable names
        intersection = mo_decl.intersection(cs_decl).intersection(ct_decl)
        if len(intersection) > 0:
            raise NotSupportedError("there are variables "
                                    "having the same name "
                                    "but different types {}".format(" , ".join(intersection)))