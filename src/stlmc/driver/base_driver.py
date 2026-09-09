"""Compatibility adapters connecting the legacy driver API to the workflow."""

import sys

from ..application.workflow import (
    VerificationWorkflow, validate_requested_goal_labels,
)
from ..cli.command import CliCommand
from ..exceptions import (
    IllegalArgumentError, NotSupportedError, ParsingError,
    SolverUnavailableError,
)
from ..parser.config_visitor import ConfigVisitor
from ..parser.model_visitor import ModelVisitor
from ..utils.print import Printer
from .abstract_driver import CmdParser, DriverFactory, Runner


class BaseDriverFactory(DriverFactory):
    def make_config_parser(self):
        return ConfigVisitor()

    def make_model_parser(self):
        return ModelVisitor()

    def make_cmd_parser(self):
        return BaseCmdParser()

    def make_runner(self):
        return BaseRunner()

    def make_printer(self):
        return Printer()


class BaseCmdParser(CliCommand, CmdParser):
    """Backward-compatible name for the CLI command loader."""


class BaseRunner(Runner):
    """Thin adapter retained for callers using the former driver API."""

    def __init__(self, workflow=None):
        self.workflow = workflow or VerificationWorkflow()

    def run(self, config_parser, model_parser, cmd_parser, printer):
        try:
            sys.setrecursionlimit(1000000)
            self.workflow.run(cmd_parser, printer)
        except (NotSupportedError, IllegalArgumentError, SolverUnavailableError):
            raise
        except SyntaxError as error:
            raise ParsingError(str(error)) from error


__all__ = [
    "BaseCmdParser", "BaseDriverFactory", "BaseRunner",
    "validate_requested_goal_labels",
]
