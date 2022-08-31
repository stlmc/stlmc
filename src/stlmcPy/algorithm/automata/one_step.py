from typing import Dict, Set

from ..algorithm import Algorithm, PathGenerator, FormulaStack
from ..runner import SmtSolverRunner
from ...constraints.aux.operations import Substitution, get_vars
from ...constraints.constraints import *
from ...encoding.smt.goal.aux import is_chi, get_hash, symbolic_sup, symbolic_inf, get_chi_depth
from ...encoding.smt.goal.stl import StlGoal
from ...encoding.smt.model.aux import indexed_var_t
from ...encoding.smt.model.stlmc_model import STLmcModel
from ...hybrid_automaton.converter import FlowStarConverter
from ...hybrid_automaton.hybrid_automaton import composition
from ...objects.configuration import Configuration
from ...objects.goal import Goal
from ...objects.model import Model
from ...solver.abstract_solver import SMTSolver
from ...util.printer import pprint


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
        print("stl v: {}, e: {}".format(len(g_a.modes), len(g_a.transitions)))
        automata = composition(m_a, g_a)
        print("v: {}, e: {}".format(len(automata.modes), len(automata.transitions)))
        fsc = FlowStarConverter()
        fsc.preprocessing(automata)
        fsc.convert(automata, bound)
        fsc.write("test")
        # print(automata)
        # print(g_a)
        # print(m_a)

        # r, m = p_runner.check_sat()
        # if r == SMTSolver.sat:
        #     return "False", 0.0, b, m

        # return "True", 0.0, bound, dict()
