from stlmcPy.core.z3Handler import z3checkSat
from stlmcPy.solver.abstract_solver import BaseSolver


class Z3Solver(BaseSolver):
    def solve(self, all_consts):
        # baseP = PART.baseCase(bound)
        #
        # # negformula is neg of goal...
        # # generate (subformula, time index) map
        # (partition, sepMap) = PART.guessPartition(negFormula, baseP)
        #
        # # full separation
        # fs = SEP.fullSeparation(negFormula, sepMap)
        #
        # originalFS = dict()
        # for (m, n) in fs[1].keys():
        #     originalFS[m] = fs[1][(m, n)]
        #
        #     # FOL translation
        # baseV = ENC.baseEncoding(partition, baseP)
        # (formulaConst, subFormulaMap) = ENC.valuation(fs[0], originalFS, ENC.Interval(True, 0.0, True, 0.0), baseV)
        #
        # # partition constraints
        # partitionConsts = PART.genPartition(baseP, fs[1], subFormulaMap)



        return z3checkSat(all_consts, 'LRA')
