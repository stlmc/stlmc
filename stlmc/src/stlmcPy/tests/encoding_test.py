import unittest

from stlmcPy.constraints.constraints import Interval, RealVal, GloballyFormula, Bool, And, FinallyFormula, Or, Real
import stlmcPy.constraints.encoding as ENC


class EncodingTest(unittest.TestCase):
    def test_finally_evaluation(self):
        # (or
        #       ( <> _[3.0, 5.0] ^ [0.0, 0.0] @ chi0)
        #       ( <> _[3.0, 5.0] ^ (0.0, TauIndex1) @ chi0)
        #       ( <> _[3.0, 5.0] ^ [TauIndex1, TauIndex1] @ chi0)
        #       ( <> _[3.0, 5.0] ^ (TauIndex1, TauIndex2) @ chi0)
        #       ( <> _[3.0, 5.0] ^ [TauIndex2, TauIndex2] @ chi0)
        #       ( <> _[3.0, 5.0] ^ (TauIndex2, 20.0) @ chi0)
        # )
        ENC.ENC_TYPES = "old"
        localTime = Interval(True, RealVal("3.0"), True, RealVal("5.0"))
        chi0 = Bool("@chi0")
        intervals = [Interval(True, RealVal("0.0"), True, RealVal("0.0")),
                     Interval(False, RealVal("0.0"), False, Real("tau_1")),
                     Interval(True, Real("tau_1"), True, Real("tau_1")),
                     Interval(False, Real("tau_1"), False, RealVal("20"))]

        f1 = FinallyFormula(localTime, intervals[0], chi0)
        f2 = FinallyFormula(localTime, intervals[1], chi0)
        f3 = FinallyFormula(localTime, intervals[2], chi0)
        f4 = FinallyFormula(localTime, intervals[3], chi0)

        '''
            (@chi0, [3.0,5.0]): (and not@newPropDecl_8 not@newPropDecl_9})
        '''
        sepMap = dict()
        x = Bool("not@newPropDecl_8")
        y = Bool("not@newPropDecl_9")
        sepMap[(chi0, localTime)] = And([x, y])

        '''
            {
                not@newPropDecl_8: [
                    ([0.0,0.0], not@newPropDecl_8_0), 
                    ((0.0,tau_1), not@newPropDecl_8_1),
                    ([tau_1,tau_1], not@newPropDecl_8_2), 
                    ((tau_1,20), not@newPropDecl_8_3)], 
                not@newPropDecl_9: [
                    ([0.0,0.0], not@newPropDecl_9_0), 
                    ((0.0,tau_1), not@newPropDecl_9_1), 
                    ([tau_1,tau_1], not@newPropDecl_9_2), 
                    ((tau_1,20), not@newPropDecl_9_3)],
            }        
        '''
        p = Bool("{}_0".format(x.id))
        q = Bool("{}_1".format(x.id))
        r = Bool("{}_2".format(x.id))
        s = Bool("{}_3".format(x.id))

        p1 = Bool("{}_0".format(y.id))
        q1 = Bool("{}_1".format(y.id))
        r1 = Bool("{}_2".format(y.id))
        s1 = Bool("{}_3".format(y.id))
        base = dict()
        base[x] = [
            (intervals[0], p),
            (intervals[1], q),
            (intervals[2], r),
            (intervals[3], s)
        ]

        base[y] = [
            (intervals[0], p1),
            (intervals[1], q1),
            (intervals[2], r1),
            (intervals[3], s1)
        ]

        formulaConst = ENC.valuation(Or([f1, f2, f3, f4]), sepMap, Interval(True, RealVal("0.0"), True, RealVal("0.0")),
                                     base)
        for c in formulaConst[0]:
            print(c)
        self.assertEqual(True, False)

    def test_globally_evaluation(self):
        # (or
        #       ( <> _[3.0, 5.0] ^ [0.0, 0.0] @ chi0)
        #       ( <> _[3.0, 5.0] ^ (0.0, TauIndex1) @ chi0)
        #       ( <> _[3.0, 5.0] ^ [TauIndex1, TauIndex1] @ chi0)
        #       ( <> _[3.0, 5.0] ^ (TauIndex1, TauIndex2) @ chi0)
        #       ( <> _[3.0, 5.0] ^ [TauIndex2, TauIndex2] @ chi0)
        #       ( <> _[3.0, 5.0] ^ (TauIndex2, 20.0) @ chi0)
        # )
        ENC.ENC_TYPES = "old"
        localTime = Interval(True, RealVal("3.0"), True, RealVal("5.0"))
        chi0 = Bool("@chi0")
        intervals = [Interval(True, RealVal("0.0"), True, RealVal("0.0")),
                     Interval(False, RealVal("0.0"), False, Real("tau_1")),
                     Interval(True, Real("tau_1"), True, Real("tau_1")),
                     Interval(False, Real("tau_1"), False, RealVal("20"))]

        f1 = GloballyFormula(localTime, intervals[0], chi0)
        f2 = GloballyFormula(localTime, intervals[1], chi0)
        f3 = GloballyFormula(localTime, intervals[2], chi0)
        f4 = GloballyFormula(localTime, intervals[3], chi0)

        '''
            (@chi0, [3.0,5.0]): (and not@newPropDecl_8 not@newPropDecl_9})
        '''
        sepMap = dict()
        x = Bool("not@newPropDecl_8")
        y = Bool("not@newPropDecl_9")
        sepMap[(chi0, localTime)] = And([x, y])

        '''
            {
                not@newPropDecl_8: [
                    ([0.0,0.0], not@newPropDecl_8_0), 
                    ((0.0,tau_1), not@newPropDecl_8_1),
                    ([tau_1,tau_1], not@newPropDecl_8_2), 
                    ((tau_1,20), not@newPropDecl_8_3)], 
                not@newPropDecl_9: [
                    ([0.0,0.0], not@newPropDecl_9_0), 
                    ((0.0,tau_1), not@newPropDecl_9_1), 
                    ([tau_1,tau_1], not@newPropDecl_9_2), 
                    ((tau_1,20), not@newPropDecl_9_3)],
            }        
        '''
        p = Bool("{}_0".format(x.id))
        q = Bool("{}_1".format(x.id))
        r = Bool("{}_2".format(x.id))
        s = Bool("{}_3".format(x.id))

        p1 = Bool("{}_0".format(y.id))
        q1 = Bool("{}_1".format(y.id))
        r1 = Bool("{}_2".format(y.id))
        s1 = Bool("{}_3".format(y.id))
        base = dict()
        base[x] = [
            (intervals[0], p),
            (intervals[1], q),
            (intervals[2], r),
            (intervals[3], s)
        ]

        base[y] = [
            (intervals[0], p1),
            (intervals[1], q1),
            (intervals[2], r1),
            (intervals[3], s1)
        ]

        formulaConst = ENC.valuation(And([f1, f2, f3, f4]), sepMap,
                                     Interval(True, RealVal("0.0"), True, RealVal("0.0")), base)
        for c in formulaConst[0]:
            print(c)
        self.assertEqual(True, False)
