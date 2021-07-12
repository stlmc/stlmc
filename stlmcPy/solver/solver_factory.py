from stlmcPy.solver.yices import YicesSolver


class SolverFactory:
    def __init__(self, solver_type):
        self.solver_type = solver_type

    def generate_solver(self):
        return YicesSolver()
