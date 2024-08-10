from ..encoding.enumerate import EnumerateAlgorithm
from ..encoding.monolithic import SmtAlgorithm
from ..encoding.reach import ReachAlgorithm
from ..objects.configuration import Configuration


class AlgorithmFactory:
    def __init__(self, config: Configuration):
        self.config = config

    def generate(self):
        common_section = self.config.get_section("common")
        is_two_step = common_section.get_value("two-step")
        is_reach = common_section.get_value("reach")
        if is_two_step == "true":
            return EnumerateAlgorithm()
        elif is_reach == "true":
            return ReachAlgorithm()
        else:
            return SmtAlgorithm()
