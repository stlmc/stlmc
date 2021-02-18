from antlr4 import FileStream, CommonTokenStream

from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.syntax.config.configLexer import configLexer
from stlmcPy.syntax.config.configParser import configParser
from stlmcPy.syntax.config.configVisitor import configVisitor


class ConfigVisitor(configVisitor):

    def __init__(self, solvers: list, solver_defaults: dict, formula_encoding_list: list, print_options: list):
        self._config_dict = dict()
        self._print_options = print_options
        self._formula_encoding = formula_encoding_list
        self._solvers = solvers
        self._solver_defaults = solver_defaults
        self._config_dict["solvers"] = list()

    def get_config_dict(self, file_name: str):
        raw_model = FileStream(file_name)
        lexer = configLexer(raw_model)
        stream = CommonTokenStream(lexer)
        parser = configParser(stream)
        tree = parser.config()
        self.visit(tree)
        return self._config_dict

    # Visit a parse tree produced by configParser#bd_conf_3.
    def visitBd_conf_3(self, ctx: configParser.Bd_conf_3Context):
        self._config_dict["lower_bound"] = int("{}".format(ctx.NUMBER(0)))
        self._config_dict["upper_bound"] = int("{}".format(ctx.NUMBER(1)))
        self._config_dict["step_bound"] = int("{}".format(ctx.NUMBER(2)))
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#bd_conf_2.
    def visitBd_conf_2(self, ctx: configParser.Bd_conf_2Context):
        self._config_dict["lower_bound"] = int("{}".format(ctx.NUMBER(0)))
        self._config_dict["upper_bound"] = int("{}".format(ctx.NUMBER(1)))
        self._config_dict["step_bound"] = 1
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#bd_conf_1.
    def visitBd_conf_1(self, ctx: configParser.Bd_conf_1Context):
        self._config_dict["lower_bound"] = int("{}".format(ctx.NUMBER()))
        self._config_dict["upper_bound"] = int("{}".format(ctx.NUMBER()))
        self._config_dict["step_bound"] = 1
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#f_conf_3.
    def visitF_conf_3(self, ctx: configParser.F_conf_3Context):
        self._config_dict["lower_formula"] = int("{}".format(ctx.NUMBER(0)))
        self._config_dict["upper_formula"] = int("{}".format(ctx.NUMBER(1)))
        self._config_dict["step_formula"] = int("{}".format(ctx.NUMBER(2)))
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#f_conf_2.
    def visitF_conf_2(self, ctx: configParser.F_conf_2Context):
        self._config_dict["lower_formula"] = int("{}".format(ctx.NUMBER(0)))
        self._config_dict["upper_formula"] = int("{}".format(ctx.NUMBER(1)))
        self._config_dict["step_formula"] = 1
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#f_conf_1.
    def visitF_conf_1(self, ctx: configParser.F_conf_1Context):
        self._config_dict["lower_formula"] = int("{}".format(ctx.NUMBER()))
        self._config_dict["upper_formula"] = int("{}".format(ctx.NUMBER()))
        self._config_dict["step_formula"] = 1
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#formula_encoding_config.
    def visitFormula_encoding_config(self, ctx: configParser.Formula_encoding_configContext):
        encoding = "{}".format(ctx.VALUE())
        if encoding in self._formula_encoding:
            self._config_dict["formula-encoding"] = encoding
        else:
            raise NotSupportedError("A given encoding type {} is not supported".format(encoding))
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#time_bound_config.
    def visitTime_bound_config(self, ctx: configParser.Time_bound_configContext):
        self._config_dict["time-bound"] = int("{}".format(ctx.NUMBER()))
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#print_config.
    def visitPrint_config(self, ctx: configParser.Print_configContext):
        print_option = "{}".format(ctx.VALUE())
        if print_option in self._print_options:
            self._config_dict["print-output"] = print_option
        else:
            raise NotSupportedError("A given print option {} is not supported".format(print_option))
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#delta_config.
    def visitDelta_config(self, ctx: configParser.Delta_configContext):
        delta = float("{}".format(ctx.NUMBER()))
        self._config_dict["delta"] = delta
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#solver_conf.
    def visitSolver_conf(self, ctx: configParser.Solver_confContext):
        solver = "{}".format(ctx.VALUE())
        if solver in self._solvers:
            solver_dict = dict()
            solver_dict["solver"] = solver
            if ctx.solver_specific() is not None:
                queue = self.visit(ctx.solver_specific())
                for q in queue:
                    solver_dict.update(self.visit(q))
            else:
                solver_dict.update(self._solver_defaults[solver])
            self._config_dict["solvers"].append(solver_dict)
        else:
            raise NotSupportedError("A given solver {} is not supported".format(solver))

    # Visit a parse tree produced by configParser#solver_specific.
    def visitSolver_specific(self, ctx:configParser.Solver_specificContext):
        queue = list()
        for c in ctx.children:
            queue.append(c)
        return queue

    # Visit a parse tree produced by configParser#yices_logic.
    def visitYices_logic(self, ctx: configParser.Yices_logicContext):
        logic_dict = dict()
        logic_dict["logic"] = "{}".format(ctx.VALUE())
        return logic_dict

    # Visit a parse tree produced by configParser#fs_single_value_list.
    def visitFs_single_value_list(self, ctx: configParser.Fs_single_value_listContext):
        return "{}".format(ctx.VALUE())

    # Visit a parse tree produced by configParser#fs_single_pair_value_list.
    def visitFs_single_pair_value_list(self, ctx: configParser.Fs_single_pair_value_listContext):
        return "{}, {}".format(ctx.VALUE(0), ctx.VALUE(1))

    # Visit a parse tree produced by configParser#fs_fixed_step.
    def visitFs_fixed_step(self, ctx: configParser.Fs_fixed_stepContext):
        fs_dict = dict()
        fs_dict["fixed steps"] = "{}".format(ctx.NUMBER())
        return fs_dict

    # Visit a parse tree produced by configParser#fs_time.
    def visitFs_time(self, ctx: configParser.Fs_timeContext):
        fs_dict = dict()
        fs_dict["time"] = "{}".format(ctx.NUMBER())
        return fs_dict

    # Visit a parse tree produced by configParser#fs_remainder.
    def visitFs_remainder(self, ctx: configParser.Fs_remainderContext):
        fs_dict = dict()
        fs_dict["remainder estimation"] = "{}".format(ctx.NUMBER1())
        return fs_dict

    # Visit a parse tree produced by configParser#fs_id_precond.
    def visitFs_id_precond(self, ctx: configParser.Fs_id_precondContext):
        fs_dict = dict()
        fs_dict["identity precondition"] = ""
        return fs_dict

    # Visit a parse tree produced by configParser#fs_gnuplot_octagon.
    def visitFs_gnuplot_octagon(self, ctx:configParser.Fs_gnuplot_octagonContext):
        var_str = ""
        for i, v in enumerate(ctx.flowstar_variable_list()):
            if i == 0:
                var_str += "{}".format(self.visit(v))
            else:
                var_str += ", {}".format(self.visit(v))
        fs_dict = dict()
        fs_dict["gnuplot octagon"] = var_str
        return fs_dict

    # Visit a parse tree produced by configParser#fs_adaptive_order.
    def visitFs_adaptive_order(self, ctx: configParser.Fs_adaptive_orderContext):
        fs_dict = dict()
        fs_dict["adaptive orders"] = "{{ min {}, max {} }}".format(ctx.NUMBER(0), ctx.NUMBER(1))
        return fs_dict

    # Visit a parse tree produced by configParser#fs_cutoff.
    def visitFs_cutoff(self, ctx: configParser.Fs_cutoffContext):
        fs_dict = dict()
        fs_dict["cutoff"] = "{}".format(ctx.NUMBER1())
        return fs_dict

    # Visit a parse tree produced by configParser#fs_precision.
    def visitFs_precision(self, ctx: configParser.Fs_precisionContext):
        fs_dict = dict()
        fs_dict["precision"] = "{}".format(ctx.NUMBER())
        return fs_dict

    # Visit a parse tree produced by configParser#fs_no_output.
    def visitFs_no_output(self, ctx: configParser.Fs_no_outputContext):
        fs_dict = dict()
        fs_dict["no output"] = ""
        return fs_dict

    # Visit a parse tree produced by configParser#fs_max_jumps.
    def visitFs_max_jumps(self, ctx: configParser.Fs_max_jumpsContext):
        fs_dict = dict()
        fs_dict["max jumps"] = "{}".format(ctx.NUMBER())
        return fs_dict
