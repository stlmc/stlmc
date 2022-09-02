from ..algorithm import Algorithm
from ...hybrid_automaton.converter import FlowStarConverter
from ...hybrid_automaton.utils import composition, get_jumps
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

        print("stl v: {}, e: {}".format(len(g_a.modes), len(get_jumps(g_a))))
        print("v: {}, e: {}".format(len(automata.modes), len(get_jumps(automata))))
        fsc = FlowStarConverter()
        fsc.convert(automata, bound)
        fsc.write("test")
        # print(automata)
        # print(g_a)
        # print(m_a)

        # r, m = p_runner.check_sat()
        # if r == SMTSolver.sat:
        #     return "False", 0.0, b, m

        # return "True", 0.0, bound, dict()
