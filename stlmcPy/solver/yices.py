from stlmcPy.core.yicesHandler import yicescheckSat
from stlmcPy.solver.abstract_solver import BaseSolver


class YicesSolver(BaseSolver):
    def solve(self, all_consts, info_dict=None):
        return yicescheckSat(all_consts, 'LRA')

    def make_assignment(self):
        pass
