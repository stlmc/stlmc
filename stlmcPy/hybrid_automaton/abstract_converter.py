'''
        < location
        id = "1"
        name = "always"
        x = "174.5"
        y = "225.5"
        width = "135.0"
        height = "73.0" >
        < invariant > x & gt;= 0 < / invariant >
        < flow > x
        ' == v &amp; v' == -g < / flow >

    < / location >

'''
import abc

from stlmcPy.constraints.constraints import Constraint
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton


class AbstractConverter:
    @abc.abstractmethod
    def convert(self, ha: HybridAutomaton):
        pass

    @staticmethod
    @abc.abstractmethod
    def make_mode_property(s_integral_i, s_forall_i, i, max_bound, ha: HybridAutomaton, sigma):
        pass

    @staticmethod
    @abc.abstractmethod
    def make_transition(s_psi_abs_i, i, max_bound, ha: HybridAutomaton, mode_p, mode_n):
        pass

    @abc.abstractmethod
    def infix(self, const: Constraint):
        pass

    @abc.abstractmethod
    def infix_reset(self, const: Constraint):
        pass
