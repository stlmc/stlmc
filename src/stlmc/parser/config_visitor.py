from typing import Union

from antlr4 import FileStream, CommonTokenStream

from .error_listener import StlmcErrorListener
from ..exception.exception import IllegalArgumentError
from ..exception.exception import NotSupportedError
from ..objects.configuration import *
from ..syntax.config.configLexer import configLexer
from ..syntax.config.configParser import configParser
from ..syntax.config.configVisitor import configVisitor


class ConfigVisitor(configVisitor):

    def __init__(self):
        # reference
        self.config: Configuration = Configuration()
        self.section_boolean_argument_dict = dict()
        self.section_argument_dict = dict()
        self.type_check_dict = dict()

        self.section_argument_dict["common"] = {
            "threshold", "bound", "time-bound",
            "solver", "goal", "time-horizon"
        }
        self.section_argument_dict["z3"] = {"logic"}
        self.section_argument_dict["yices"] = {"logic"}
        self.section_argument_dict["dreal"] = {"ode-order", "ode-step", "executable-path"}

        self.type_check_dict["common"] = {
            ("threshold", "float"), ("bound", "integer"), ("time-bound", "float"),
            ("solver", frozenset({"z3", "yices", "dreal"})), ("goal", "string"), ("time-horizon", "float")
        }
        self.type_check_dict["z3"] = {("logic", frozenset({"QF_NRA", "QF_LRA"}))}
        self.type_check_dict["yices"] = {("logic", frozenset(["QF_NRA", "QF_LRA"]))}
        self.type_check_dict["dreal"] = {("ode-order", "float"), ("ode-step", "float"), ("executable-path", "path")}

        self.section_boolean_argument_dict["common"] = {"two-step", "parallel", "visualize", "verbose", "reach", "only-loop"}
        self.section_boolean_argument_dict["z3"] = set()
        self.section_boolean_argument_dict["yices"] = set()
        self.section_boolean_argument_dict["dreal"] = set()

        self.section_names: List[str] = ["common", "z3", "yices", "dreal"]

        self.section_mandatory_dict = dict()
        self.section_mandatory_dict["common"] = {"bound", "time-bound"}
        self.section_mandatory_dict["z3"] = set()
        self.section_mandatory_dict["yices"] = set()
        self.section_mandatory_dict["dreal"] = {"ode-step", "ode-order", "executable-path"}

        self.section_selectable_dict: Dict[str, List[Set[str]]] = dict()
        self.section_selectable_dict["common"] = list()
        self.section_selectable_dict["z3"] = list()
        self.section_selectable_dict["yices"] = list()
        self.section_selectable_dict["dreal"] = list()

    def get_missing_arguments(self, config: Configuration) -> Dict[str, Set[str]]:
        missing_dict = dict()
        for section in config.sections:
            if section.name not in self.section_names:
                raise IllegalArgumentError("\"{}\" is not a valid section name".format(section.name))

            mandatory = self.section_argument_dict[section.name]

            is_skip = False
            choices = self.section_selectable_dict[section.name]
            for choice in choices:
                if choice.issubset(set(section.arguments.keys())):
                    is_skip = True
                    break

            if is_skip:
                continue

            missing = mandatory.difference(set(section.arguments.keys()))
            if len(missing) > 0:
                missing_dict[section.name] = missing
        return missing_dict

    def generate_cmd_args(self):
        cmds = set()
        for section_name in self.section_argument_dict:
            cmds.update(self.section_argument_dict[section_name])

        bool_cmds = set()
        for section_name in self.section_boolean_argument_dict:
            bool_cmds.update(self.section_boolean_argument_dict[section_name])
        return cmds, bool_cmds

    def parse_from_file(self, file_name: str, base: Union[Configuration, None] = None) -> Configuration:
        self.config = Configuration()
        if base is not None:
            self.config = base

        raw_model = FileStream(file_name)
        lexer = configLexer(raw_model)
        stream = CommonTokenStream(lexer)
        parser = configParser(stream)
        parser.removeErrorListeners()
        cfg_err_listener = StlmcErrorListener()
        cfg_err_listener.name = file_name
        parser.addErrorListener(cfg_err_listener)
        tree = parser.config()
        self.visit(tree)

        # discard an empty string as a value
        for section in self.config.sections:
            for arg_name in section.arguments:
                if section.arguments[arg_name] == "":
                    del section.arguments[arg_name]

        # set mandatory information
        self.config.set_section_mandatory_dict(self.section_mandatory_dict)
        # set type check information
        self.config.set_type_check_dict(self.type_check_dict)
        return self.config

    def find_parent(self, name: str):
        if name in self.config.sections_by_name:
            return self.config.sections_by_name[name]
        return None

    # Visit a parse tree produced by configParser#config.
    def visitConfig(self, ctx: configParser.ConfigContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#basic_section.
    def visitBasic_section(self, ctx: configParser.Basic_sectionContext):
        name = ctx.VALUE().getText()
        if name not in self.section_names:
            raise NotSupportedError("\"{}\" is not a valid section name".format(name))

        section = Section()
        section.name = name
        section.arguments = self.visit(ctx.args())

        if section.name in self.section_mandatory_dict:
            section.mandatory.extend(self.section_mandatory_dict[section.name])

        self.config.add_section(section)

        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#extend_section.
    def visitExtend_section(self, ctx: configParser.Extend_sectionContext):
        name = ctx.VALUE().getText()
        if name not in self.section_names:
            raise NotSupportedError("\"{}\" is not a valid section name".format(name))

        parents: List[Section] = list()
        parent_names = self.visit(ctx.names())
        for parent_name in parent_names:
            parent_section = self.find_parent(parent_name)
            if parent_section is None:
                raise NotSupportedError("cannot find definition of a parent {}".format(parent_name))
            parents.append(parent_section)

        section = Section()
        section.name = name
        section.parent_names.extend(parent_names)

        if section.name in self.section_mandatory_dict:
            section.mandatory.extend(self.section_mandatory_dict[section.name])

        for parent in parents:
            section.arguments.update(parent.arguments)

        section.arguments.update(self.visit(ctx.args()))
        self.config.add_section(section)

        return self.visitChildren(ctx)

    # Visit a parse tree produced by configParser#list_of_name.
    def visitList_of_name(self, ctx: configParser.List_of_nameContext):
        names = [ctx.VALUE().getText()]
        names.extend(self.visit(ctx.names()))
        return names

    # Visit a parse tree produced by configParser#single_names.
    def visitSingle_names(self, ctx: configParser.Single_namesContext):
        return [ctx.VALUE().getText()]

    # Visit a parse tree produced by configParser#args.
    def visitArgs(self, ctx: configParser.ArgsContext):
        args_dict = dict()
        for arg_assn_ctx in ctx.arg_assn():
            arg, value = self.visit(arg_assn_ctx)
            args_dict[arg] = value
        return args_dict

    # Visit a parse tree produced by configParser#arg_assn.
    def visitArg_assn(self, ctx: configParser.Arg_assnContext):
        return self.visit(ctx.arg()), self.visit(ctx.value())

    # Visit a parse tree produced by configParser#arg.
    def visitArg(self, ctx: configParser.ArgContext):
        return ctx.VALUE().getText()

    # Visit a parse tree produced by configParser#string_val.
    def visitString_val(self, ctx: configParser.String_valContext):
        return "\"{}\"".format(ctx.VALUE().getText())

    # Visit a parse tree produced by configParser#multi_string_val.
    def visitMulti_string_val(self, ctx: configParser.Multi_string_valContext):
        vals = self.visit(ctx.varible_names())
        return ",".join(vals)

    # Visit a parse tree produced by configParser#runall_val.
    def visitRunall_val(self, ctx: configParser.Runall_valContext):
        return ctx.RUNALL().getText()

    # Visit a parse tree produced by configParser#runlabeled_only.
    def visitRunlabeled_only(self, ctx: configParser.Runlabeled_onlyContext):
        return ctx.RUNLABELED().getText()

    # Visit a parse tree produced by configParser#number_val.
    def visitNumber_val(self, ctx: configParser.Number_valContext):
        return ctx.NUMBER().getText()

    # Visit a parse tree produced by configParser#empty_val.
    def visitEmpty_val(self, ctx: configParser.Empty_valContext):
        return ""

    # Visit a parse tree produced by configParser#list_of_variable_names.
    def visitList_of_variable_names(self, ctx: configParser.List_of_variable_namesContext):
        variables = [ctx.VALUE().getText()]
        variables.extend(self.visit(ctx.varible_names()))
        return variables

    # Visit a parse tree produced by configParser#single_variable_name.
    def visitSingle_variable_name(self, ctx: configParser.Single_variable_nameContext):
        return [ctx.VALUE().getText()]
