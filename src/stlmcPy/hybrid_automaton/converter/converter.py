import abc

from ..utils import *


class Converter:
    @abc.abstractmethod
    def convert(self, ha: HybridAutomaton):
        pass

    @abc.abstractmethod
    def write(self, file_name: str):
        pass


class ConverterFactory:
    SE = 10
    FS = 11

    @staticmethod
    def generate_converter(converter_type: int) -> Converter:
        assert ConverterFactory.SE <= converter_type <= ConverterFactory.FS
        if converter_type == ConverterFactory.SE:
            return SpaceExConverter()
        elif converter_type == ConverterFactory.FS:
            return FlowStarConverter()
        else:
            raise NotImplementedError("unsupported converter type")
