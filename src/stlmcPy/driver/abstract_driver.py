import abc

from ..parser.config_visitor import ConfigVisitor
from ..parser.model_parser import ModelParser
from ..util.printer import *


class StlModelChecker:
    def __init__(self):
        self.config_parser = None
        self.model_parser = None
        self.cmd_parser = None
        self.runner = None
        self.logger = None
        self.printer = None

    def create_env(self, df: 'DriverFactory'):
        self.config_parser = df.make_config_parser()
        self.model_parser = df.make_model_parser()
        self.cmd_parser = df.make_cmd_parser()
        self.runner = df.make_runner()
        self.printer = df.make_printer()

    def run(self):
        self.runner.run(self.config_parser, self.model_parser, self.cmd_parser, self.printer)


class DriverFactory:
    def __init__(self):
        pass

    @abc.abstractmethod
    def make_config_parser(self) -> ConfigVisitor:
        pass

    @abc.abstractmethod
    def make_model_parser(self) -> ModelParser:
        pass

    @abc.abstractmethod
    def make_cmd_parser(self) -> 'CmdParser':
        pass

    @abc.abstractmethod
    def make_runner(self) -> 'Runner':
        pass

    @abc.abstractmethod
    def make_printer(self) -> Printer:
        pass


class Runner:
    @abc.abstractmethod
    def run(self, config_parser: 'ConfigVisitor', model_parser: 'ModelParser',
            cmd_parser: 'CmdParser', printer: Printer):
        pass


class CmdParser:
    @abc.abstractmethod
    def parse(self):
        pass

    @abc.abstractmethod
    def get_config(self):
        pass
