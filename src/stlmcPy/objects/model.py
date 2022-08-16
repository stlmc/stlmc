import abc

from ..constraints.constraints import Variable
from ..encoding.base_encoder import Encoder


class Model(Encoder):
    @abc.abstractmethod
    def encode(self):
        pass

    @abc.abstractmethod
    def get_abstraction(self):
        pass
