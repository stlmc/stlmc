from .runner import ParallelSmtSolverRunner
from .smt.two_step import TwoStepAlgorithm
from .automata.one_step import OneStepAlgorithm
# from ..encoding.monolithic import SmtAlgorithm
# from ..encoding.reach import ReachAlgorithm
from ..objects.configuration import Configuration


class AlgorithmFactory:
    def __init__(self, config: Configuration):
        self.config = config

    def generate(self):
        common_section = self.config.get_section("common")
        is_two_step = common_section.get_value("two-step")
        is_parallel = common_section.get_value("parallel")
        encoding = common_section.get_value("encoding")

        if encoding == "smt":
            is_reach = "false"
            if is_two_step == "true":
                if is_parallel:
                    return TwoStepAlgorithm(self.config, ParallelSmtSolverRunner(25))
                else:
                    return TwoStepAlgorithm(self.config, ParallelSmtSolverRunner(1))
        else:
            return OneStepAlgorithm(self.config)
        # elif is_reach == "true":
        #     return ReachAlgorithm()
        # else:
        #     return SmtAlgorithm()
