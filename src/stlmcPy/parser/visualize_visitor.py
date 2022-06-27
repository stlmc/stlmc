from typing import Dict, Set

from antlr4 import FileStream, CommonTokenStream

from .error_listener import StlmcErrorListener
from ..syntax.visualize.visualizeLexer import visualizeLexer
from ..syntax.visualize.visualizeParser import visualizeParser
from ..syntax.visualize.visualizeVisitor import visualizeVisitor


def gen_id():
    id_num = 0
    while True:
        yield id_num
        id_num += 1


class VisualizeConfigPaser(visualizeVisitor):
    def __init__(self):
        self.group: Dict[int, Set[str]] = dict()
        self.output = ""
        self.gen = gen_id()
        self.supported_outputs = ["html", "pdf"]

    def read(self, file_name):
        raw_model = FileStream(file_name)
        lexer = visualizeLexer(raw_model)
        stream = CommonTokenStream(lexer)
        parser = visualizeParser(stream)
        parser.removeErrorListeners()
        vis_err_listener = StlmcErrorListener()
        vis_err_listener.name = "(visual config) {}".format(file_name)
        parser.addErrorListener(vis_err_listener)
        tree = parser.vis_config()
        return self.visit(tree)

    # Visit a parse tree produced by visualizeParser#vis_config.
    def visitVis_config(self, ctx: visualizeParser.Vis_configContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by visualizeParser#body.
    def visitBody(self, ctx: visualizeParser.BodyContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by visualizeParser#output.
    def visitOutput(self, ctx: visualizeParser.OutputContext):
        output = ctx.VARIABLE().getText()
        if output in self.supported_outputs:
            self.output = output
        else:
            raise ValueError("visualize configuration error: output format {} does not supported".format(output))

    # Visit a parse tree produced by visualizeParser#group.
    def visitGroup(self, ctx: visualizeParser.GroupContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by visualizeParser#other_group_list.
    def visitOther_group_list(self, ctx: visualizeParser.Other_group_listContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by visualizeParser#base_group.
    def visitBase_group(self, ctx: visualizeParser.Base_groupContext):
        # return self.visitChildren(ctx)
        self.group[next(self.gen)] = self.visit(ctx.variable_list())

    # Visit a parse tree produced by visualizeParser#empty_group.
    def visitEmpty_group(self, ctx: visualizeParser.Empty_groupContext):
        return

    # Visit a parse tree produced by visualizeParser#other_var_list.
    def visitOther_var_list(self, ctx: visualizeParser.Other_var_listContext):
        left = self.visit(ctx.variable_list()[0])
        right = self.visit(ctx.variable_list()[1])
        var_set = set()
        var_set.update(left)
        var_set.update(right)
        return var_set

    # Visit a parse tree produced by visualizeParser#empty_var_list.
    def visitEmpty_var_list(self, ctx: visualizeParser.Empty_var_listContext):
        return set()

    # Visit a parse tree produced by visualizeParser#base_var_list.
    def visitBase_var_list(self, ctx: visualizeParser.Base_var_listContext):
        return {ctx.VARIABLE().getText()}
