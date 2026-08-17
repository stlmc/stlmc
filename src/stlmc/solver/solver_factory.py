from ..solver.yices import YicesSolver
from ..solver.z3 import Z3Solver
from ..solver.dreal import dRealSolver


class SolverFactory:
    def __init__(self):
        self.solver_type = None

    def generate_solver(self, config):
        common_section = config.get_section("common")
        self.solver_type = common_section.get_value("solver")
        if self.solver_type == 'z3':
            return Z3Solver()
        elif self.solver_type == 'dreal':
            return dRealSolver()
        return YicesSolver()
