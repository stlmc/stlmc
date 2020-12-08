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

from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton


class AbstractConverter:
    @abc.abstractmethod
    def convert(self, ha: HybridAutomaton):
        pass
