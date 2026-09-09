from ..algorithms.two_step import TwoStepAlgorithm
from ..encoding.model_checking import ModelCheckingAlgorithm
from ..algorithms.one_step import OneStepAlgorithm
from ..encoding.path import make_path_provider
from ..objects.configuration import Configuration
from .options import RunOptions


class AlgorithmFactory:
    def __init__(self, config: Configuration, formula_solver_factory):
        self.config = config
        self.formula_solver_factory = formula_solver_factory

    def generate(self):
        options = RunOptions.from_configuration(self.config)
        path_provider = make_path_provider(options.path_strategy)
        if options.two_step:
            continuous_solving = TwoStepAlgorithm(
                path_provider, self.formula_solver_factory, options
            )
        else:
            continuous_solving = OneStepAlgorithm(
                path_provider, self.formula_solver_factory, options
            )
        return ModelCheckingAlgorithm(continuous_solving)
