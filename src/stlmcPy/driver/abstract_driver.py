import abc

from ..parser.config_visitor import ConfigVisitor
from ..parser.model_visitor import ModelVisitor

from ..util.logger import Logger
from ..util.print import *


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
        self.logger = df.make_logger()
        self.printer = df.make_printer()

    def run(self):
        self.runner.run(self.config_parser, self.model_parser, self.cmd_parser,
                        self.logger, self.printer)


class DriverFactory:
    def __init__(self):
        pass

    @abc.abstractmethod
    def make_config_parser(self) -> ConfigVisitor:
        pass

    @abc.abstractmethod
    def make_model_parser(self) -> ModelVisitor:
        pass

    @abc.abstractmethod
    def make_cmd_parser(self) -> 'CmdParser':
        pass

    @abc.abstractmethod
    def make_runner(self) -> 'Runner':
        pass

    @abc.abstractmethod
    def make_logger(self) -> Logger:
        pass

    @abc.abstractmethod
    def make_printer(self) -> Printer:
        pass


class Runner:
    @abc.abstractmethod
    def run(self, config_parser: 'ConfigVisitor', model_parser: 'ModelVisitor',
            cmd_parser: 'CmdParser', logger: Logger, printer: Printer):
        pass


class CmdParser:
    @abc.abstractmethod
    def parse(self):
        pass

    @abc.abstractmethod
    def get_config(self):
        pass
