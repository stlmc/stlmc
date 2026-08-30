from ..encoding.enumerate import TwoStepAlgorithm
from ..encoding.model_checking import ModelCheckingAlgorithm
from ..encoding.monolithic import OneStepAlgorithm
from ..encoding.path import make_path_provider
from ..objects.configuration import Configuration


class AlgorithmFactory:
    def __init__(self, config: Configuration, formula_solver_factory):
        self.config = config
        self.formula_solver_factory = formula_solver_factory

    def generate(self):
        common_section = self.config.get_section("common")
        is_two_step = common_section.get_value("two-step")
        path_provider = make_path_provider(
            common_section.get_value("path-strategy")
        )
        if is_two_step == "true":
            continuous_solving = TwoStepAlgorithm(
                path_provider, self.formula_solver_factory
            )
        else:
            continuous_solving = OneStepAlgorithm(
                path_provider, self.formula_solver_factory
            )
        return ModelCheckingAlgorithm(continuous_solving)
