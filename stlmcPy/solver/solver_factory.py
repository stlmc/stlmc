from stlmcPy.solver.hylaa import HylaaSolver
from stlmcPy.solver.yices import YicesSolver
from stlmcPy.solver.z3 import Z3Solver


class SolverFactory:
    def __init__(self, solver_type):
        self.solver_type = solver_type

    def generate_solver(self):
        if self.solver_type == 'z3':
            return Z3Solver()
        elif self.solver_type == 'yices':
            return YicesSolver()
        elif self.solver_type == 'hylaa':
            return HylaaSolver()
