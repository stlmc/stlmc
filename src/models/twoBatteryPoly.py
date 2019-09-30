import os, sys
from stlMC import *
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))

# STL
from .batterySTL import testcaseSTL

# reachability goal
goal = And(Bool('mf'), Not(Bool('ms')), Bool('mt'))

# some constants 
K = RealVal(2.0)
C = RealVal(0.166)

#On: 1, Off: 0, Dead: -1

class BatteryPoly(Model):
    def __init__(self):
        # modes
        mf = Bool('mf')
        ms = Bool('ms')
        mt = Bool('mt')

        # variables
        d1 = Real('d1')
        d2 = Real('d2')
        g1 = Real('g1')
        g2 = Real('g2')
        constd1 = Real('constd1')
        constd2 = Real('constd2')

        # flow conditions
        flow = {\
                And(Not(mf), Not(ms), Not(mt)): \
                {constd1: RealVal(0), constd2: RealVal(0), d1: (RealVal(0.5) / C) - (K * constd1), d2: (RealVal(0.5) / C) - (K * constd2), g1: -RealVal(0.5), g2: -RealVal(0.5)}, \
                And(Not(mf), Not(ms), mt): \
                {constd1: RealVal(0), constd2: RealVal(0), d1: (RealVal(1) / C) - (K * constd1), d2: -(K * constd2), g1: -RealVal(1), g2: RealVal(0)}, \
                And(Not(mf), ms, Not(mt)): \
                {constd1: RealVal(0), constd2: RealVal(0), d1: -(K * constd1), d2: (RealVal(1) / C) - (K * constd2), g1: RealVal(0), g2: -RealVal(1)}, \
                And(Not(mf), ms, mt): \
                {constd1: RealVal(0), constd2: RealVal(0), d1: RealVal(0), d2: (RealVal(1) / C) - (K * constd2), g1: RealVal(0), g2: -RealVal(1)}, \
                And(mf, Not(ms), Not(mt)): \
                {constd1: RealVal(0), constd2: RealVal(0), d1: (RealVal(1) / C) - (K * constd1), d2: RealVal(0), g1: -RealVal(1), g2: RealVal(0)}, \
               And(mf, Not(ms), mt): \
               {constd1: RealVal(0), constd2: RealVal(0), d1: RealVal(0), d2: RealVal(0), g1: RealVal(0), g2: RealVal(0)}}
 
        # initial conditions
        init = And(And(Not(mf), Not(ms), Not(mt)), g1 == RealVal(8.5), d1 == RealVal(0), g2 == RealVal(7.5), d2 == RealVal(0), constd1 == d1, constd2 == d2)

        # set the interval bound to the variables
        vars = {constd1: (-10, 10), constd2: (-10, 10), d1: (-10, 10), d2: (-10, 10), g1: (-10, 10), g2: (-10, 10)} 
        # invariant conditions
        inv = {\
               And(Not(mf), Not(ms), Not(mt)): BoolVal(True), \
               And(Not(mf), Not(ms), mt): BoolVal(True), \
               And(Not(mf), ms, Not(mt)): BoolVal(True), \
               And(Not(mf), ms, mt): BoolVal(True), \
               And(mf, Not(ms), Not(mt)): BoolVal(True), \
               And(mf, Not(ms), mt): BoolVal(True)}


        # jump conditions
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        mtNext = NextVar(mt)
        d1Next = NextVar(d1)
        d2Next = NextVar(d2)
        constd1Next = NextVar(constd1)
        constd2Next = NextVar(constd2)
        g1Next = NextVar(g1)
        g2Next = NextVar(g2)

        jump = {\
                And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): \
                And(And(Not(mfNext), Not(msNext), mtNext), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
                And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): \
                And(And(Not(mfNext), msNext, Not(mtNext)), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
                And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): \
                And(And(Not(mfNext), msNext, mtNext), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
                And(g1 <= (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): \
                And(And(Not(mfNext), msNext, mtNext), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
                And(g1 > (RealVal(1) - C) * d1, g2 <= (RealVal(1) - C) * d2): \
                And(And(mfNext, Not(msNext), Not(mtNext)), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
                And(g1 <= (RealVal(1) - C) * d1, g2 <= (RealVal(1) - C) * d2): \
                And(And(mfNext, Not(msNext), mtNext), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2)}


        # STL propositions
        proBFL = Bool('bfonel')
        proBSL = Bool('bftwol')
        proBSR = Bool('bftwor')
        proF = Bool('fone')
        proFourL = Bool('ffourp')
        proFourR = Bool('ffourq')

        prop = {proBFL: And(Not(mf), Not(ms), Not(mt)), \
                proBSL: Or(g1 >= RealVal(0), g2 >= RealVal(0)), \
                proBSR: And(mf, Not(ms), mt), \
                proF: d1 > RealVal(1.4), \
                proFourL: d1 > RealVal(0.5), proFourR: d2 > RealVal(0.5)}

        super().__init__(vars, init, flow, inv, jump, prop, "QF_NRA")

