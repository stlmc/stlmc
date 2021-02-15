from stlmcPy.solver.c2e2 import C2E2SolverUnsatCore
from stlmcPy.solver.flowstar import FlowStarSolverUnsatCore
from stlmcPy.solver.hylaa import HylaaSolverNaive, HylaaSolverReduction, HylaaSolverUnsatCore
from stlmcPy.solver.spaceex import SpaceExSolverUnsatCore, SpaceExSolverNaive
from stlmcPy.solver.yices import YicesSolver
from stlmcPy.solver.z3 import Z3Solver
from stlmcPy.solver.dreal import dRealSolver


class SolverFactory:
    def __init__(self, solver_type):
        self.solver_type = solver_type

    def generate_solver(self):
        if self.solver_type == 'z3':
            return Z3Solver()
        elif self.solver_type == 'yices':
            return YicesSolver()
        elif self.solver_type == 'dreal':
            return dRealSolver()
        elif self.solver_type == 'hylaa':
            return HylaaSolverNaive()
        elif self.solver_type == 'hylaa-reduction':
            return HylaaSolverReduction()
        elif self.solver_type == 'hylaa-unsat-core':
            return HylaaSolverUnsatCore()
        elif self.solver_type == 'spaceex':
            return SpaceExSolverUnsatCore()
        elif self.solver_type == 'flowstar':
            return FlowStarSolverUnsatCore()
        elif self.solver_type == 'c2e2':
            return C2E2SolverUnsatCore()
