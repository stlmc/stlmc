from .new_dreal import newDRealSolver
from ..solver.yices import YicesSolver
from ..solver.z3 import Z3Solver
from ..solver.dreal import dRealSolver
from ..solver.flowstar import FlowStarSolverUnsatCoreMerging, FlowStarSolverUnsatCore
from ..solver.spaceex import *


class SolverFactory:
    def __init__(self):
        self.solver_type = None

    def generate_solver(self, config):
        common_section = config.get_section("common")
        self.solver_type = common_section.get_value("solver")
        is_reach = common_section.get_value("reach")

        if self.solver_type == 'z3':
            return Z3Solver()
        elif self.solver_type == 'dreal':
            if is_reach == "true":
                return newDRealSolver()
            else:
                return dRealSolver()
        elif 'flowstar' in self.solver_type:
            return FlowStarSolverUnsatCore()
        elif "spaceex" in self.solver_type:
            return SpaceExSolverUnsatCore()

        return YicesSolver()
