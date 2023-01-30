import os
import pickle

from ..algorithm import Algorithm
from ...encoding.automata.goal.ha_converter import HaBoundProcessor
from ...hybrid_automaton.converter.flowstar import FlowStarConverter
from ...hybrid_automaton.converter.juliareach import JuliaReachConverter
from ...hybrid_automaton.converter.spaceex import SpaceExConverter
from ...hybrid_automaton.converter.stlmc import StlmcConverter
from ...hybrid_automaton.utils import composition, get_jumps, print_ha_size
from ...objects.configuration import Configuration
from ...objects.goal import Goal
from ...objects.model import Model
from ...solver.abstract_solver import SMTSolver


class OneStepAlgorithm(Algorithm):
    def __init__(self, config: Configuration):
        self._config = config
        self._ha_bound_proc = HaBoundProcessor(self._config)

    def run(self, model: Model, goal: Goal, solver: SMTSolver):
        solver.reset()

        common_section = self._config.get_section("common")
        solver_ty = common_section.get_value("solver")
        file_name = common_section.get_value("file")
        file_name = os.path.basename(file_name)
        name, ext = os.path.splitext(file_name)

        m_a, g_a = model.encode(), goal.encode()
        # print(g_a)
        # print(m_a)
        automata = composition(m_a, g_a)
        self._ha_bound_proc.add_bounds(automata)

        print_ha_size("stl", g_a)
        print_ha_size("model", m_a)
        print_ha_size("composed", automata)

        if solver_ty == "flowstar":
            # flowstar
            converter = FlowStarConverter(self._config)
        elif solver_ty == "juliareach":
            # juliareach
            converter = JuliaReachConverter(self._config)
        elif solver_ty == "spaceex":
            # spaceex
            converter = SpaceExConverter(self._config)
        elif solver_ty == "stlmc":
            converter = StlmcConverter(self._config)
        else:
            raise Exception("{} is not a valid reachable solver".format(solver_ty))

        converter.convert(automata)
        converter.write(name)

        # r, m = p_runner.check_sat()
        # if r == SMTSolver.sat:
        #     return "False", 0.0, b, m

        # return "True", 0.0, bound, dict()
