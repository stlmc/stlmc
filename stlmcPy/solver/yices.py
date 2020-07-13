from stlmcPy.core.yicesHandler import yicescheckSat
from stlmcPy.solver.abstract_solver import BaseSolver


class YicesSolver(BaseSolver):
    def solve(self, all_consts):
        return yicescheckSat(all_consts, 'LRA')
