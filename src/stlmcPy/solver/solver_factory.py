from ..solver.c2e2 import C2E2SolverUnsatCore
from ..solver.hylaa import HylaaSolverNaive, HylaaSolverReduction, HylaaSolverUnsatCore
from ..solver.spaceex import SpaceExSolverUnsatCore, SpaceExSolverNaive
from ..solver.ssmt import SsmtSolver
from ..solver.yices import YicesSolver
from ..solver.z3 import Z3Solver
from ..solver.dreal import DrealSolver


class SolverFactory:
    def __init__(self):
        self.solver_type = None

    def generate_solver(self, config):
        common_section = config.get_section("common")
        self.solver_type = common_section.get_value("solver")
        is_reach = "false"

        if self.solver_type == 'z3':
            return Z3Solver(config)
        elif self.solver_type == 'dreal':
            if is_reach == "true":
                return newDRealSolver()
            else:
                return DrealSolver(config)
        elif self.solver_type == 'yices':
            return YicesSolver(config)
        elif self.solver_type == 'dreal':
            return DrealSolver(config)
        elif self.solver_type == 'hylaa':
            return HylaaSolverNaive()
        elif self.solver_type == 'hylaa-reduction':
            return HylaaSolverReduction()
        elif self.solver_type == 'hylaa-unsat-core':
            return HylaaSolverUnsatCore()
        elif self.solver_type == 'spaceex':
            return SpaceExSolverUnsatCore()
        elif self.solver_type == 'c2e2':
            return C2E2SolverUnsatCore()
        elif self.solver_type == 'ssmt':
            return SsmtSolver()
        return YicesSolver(config)
