import unittest

from stlmcPy.constraints.constraints import Interval, RealVal
from stlmcPy.constraints.interval import intervalConst


class IntervalTestCase(unittest.TestCase):
    def test_simple(self):

        j = Interval(False, RealVal("2"), False, RealVal("4"))
        k = Interval(True, RealVal("0"), False, RealVal("5"))
        i = Interval(True, RealVal("1"), True, RealVal("3"))

        print(intervalConst(j, k, i))



        self.assertEqual(True, False)

    def test_simple1(self):

        j = Interval(True, RealVal("0"), True, RealVal("0"))
        k = Interval(True, RealVal("0"), True, RealVal("0"))
        i = Interval(True, RealVal("3"), True, RealVal("5"))

        print(intervalConst(j, k, i))



        self.assertEqual(True, False)


