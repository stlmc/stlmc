from stlmcPy.solver.abstract_solver import BaseSolver


class SsmtSolver(BaseSolver):
    def solve(self, all_consts=None, cont_vars_dict=None, boolean_abstract_dict=None):
        print(all_consts)
        return "False"

    def make_assignment(self):
        pass
