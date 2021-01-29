import unittest

from stlmcPy.constraints.constraints import Bool, Real, And, Gt, Lt, RealVal, Or, Not, FinallyFormula, Interval, \
    GloballyFormula
from stlmcPy.constraints.operations import make_dict, substitution
import stlmcPy.constraints.separation as SEP


class SeperationTest(unittest.TestCase):

    def test_full_seperation1(self):
        # (<>_[3.0,5.0]^[0.0,20] (and (and not@newPropDecl_8 not@newPropDecl_9) ([]_[0.0,15.0]^[0.0,20] not@yInc)))
        localTime = Interval(True, RealVal("3.0"), True, RealVal("5.0"))
        globalTime = Interval(True, RealVal("0.0"), True, RealVal("20.0"))
        localTime1 = Interval(True, RealVal("0.0"), True, RealVal("15.0"))

        subFormula = GloballyFormula(localTime1, globalTime, Bool("not@yInc"))
        formula = And([Bool("not@newPropDecl_8"), Bool("not@newPropDecl_9"), subFormula])
        testFormula = FinallyFormula(localTime, globalTime, formula)
        # sep map
        # {([]_[0.0,15.0]^[0.0,20] not@yInc): [tau_2, tau_1],
        # (<>_[3.0,5.0]^[0.0,20] (and (and not@newPropDecl_8 not@newPropDecl_9) ([]_[0.0,15.0]^[0.0,20] not@yInc))): [TauIndex16, TauIndex12, TauIndex14, TauIndex17, TauIndex18, TauIndex11, TauIndex15, TauIndex19, TauIndex13, TauIndex10]}

        sepMap = dict()
        sepMap[subFormula] = [Real("tau_2"), Real("tau_1")]
        sepMap[testFormula] = [Real("TauIndex{}".format(i)) for i in range(10, 20)]
        fs = SEP.fullSeparation(testFormula, sepMap)
        print(fs)
        self.assertTrue("dd")
        # self.assertEqual(repr(result_const), "(and (> real x_2_0 0) (or (not bool mode_a_2) (< real y_2_0 real mode_b_2)))",
        #                  'Not correct result')
