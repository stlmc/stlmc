import pickle

from ..algorithm import Algorithm
from ...hybrid_automaton.converter.flowstar import FlowStarConverter
from ...hybrid_automaton.converter.juliareach import JuliaReachConverter
from ...hybrid_automaton.utils import composition, get_jumps, print_ha_size
from ...objects.configuration import Configuration
from ...objects.goal import Goal
from ...objects.model import Model
from ...solver.abstract_solver import SMTSolver


class OneStepAlgorithm(Algorithm):
    def __init__(self, config: Configuration):
        self._config = config

    def run(self, model: Model, goal: Goal, solver: SMTSolver):
        solver.reset()

        # p_runner = self._runner

        common_section = self._config.get_section("common")
        bound = int(common_section.get_value("bound"))

        m_a, g_a = model.encode(), goal.encode()
        # print(g_a)
        # print(m_a)
        automata = composition(m_a, g_a)

        print_ha_size("stl", g_a)
        print_ha_size("model", m_a)
        print_ha_size("composed", automata)
        # fsc = FlowStarConverter(self._config)
        # fsc.convert(automata)
        # fsc.write("test")
        jlc = JuliaReachConverter(self._config)
        jlc.convert(automata)
        jlc.write("test")

        # r, m = p_runner.check_sat()
        # if r == SMTSolver.sat:
        #     return "False", 0.0, b, m

        # return "True", 0.0, bound, dict()
