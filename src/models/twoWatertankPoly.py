import os, sys
from stlMC import *
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))


# STL
from .watertankSTL import testcaseSTL

# reachability goal
goal = Real('sx') > RealVal(5.5)


# some constants
gH = RealVal(5.0)
g = RealVal(9.806)
a = RealVal(0.025)

A1 = RealVal(8.0)
A2 = RealVal(9.0)
q1 = RealVal(0.025)
q2 = RealVal(0.015)

class WatertankPoly(Model):
    def __init__(self):
        # modes
        mf = Bool('mf')
        ms = Bool('ms')

        # variables
        fx = Real('fx')
        sx = Real('sx')
        constfx = Real('constfx')
        constsx = Real('constsx')

        # flow conditions
        fxOff = -a * RealVal(2) * g / RealVal(2) * constfx / (RealVal(2) * A1) 
        fxOn = (q1 - a * RealVal(2) * g / RealVal(2) * constfx) / (RealVal(2) * A1)
        sxOff = (a * RealVal(2) * g / RealVal(2) * (constfx - constsx)) / (RealVal(2) * A2)
        sxOn = (q2 + a * RealVal(2) * g / RealVal(2) * (constfx - constsx)) / (RealVal(2) * A2)

        flow = {\
                And(Not(mf), Not(ms)): \
                {fx: fxOff, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                \
                And(Not(mf), ms): \
                {fx: fxOff, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}, \
                \
                And(mf, Not(ms)): \
                {fx: fxOn, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                \
                And(mf, ms): \
                {fx: fxOn, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}}

        # initial conditions
        init = And(mf, ms, fx >= gH - RealVal(0.1), fx <= gH + RealVal(0.1), sx >= gH - RealVal(0.1), sx <= gH + RealVal(0.1), And(constfx == fx, constsx == sx))

        # set the interval bound to the variables
        vars = {fx: (0, 10), sx: (0, 10), constfx: (0, 10), constsx: (0, 10)}
        # invariant conditions
        inv = {And(Not(mf), Not(ms)): And(fx > RealVal(0), sx > RealVal(0)), \
               And(Not(mf), ms): And(fx > RealVal(0), sx <= A2), \
               And(mf, Not(ms)): And(fx <= A1, sx > RealVal(0) ), \
               And(mf, ms):  And(fx <= A1, sx <= A2)}

        # jump conditions
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        constfxNext = NextVar(constfx)
        constsxNext = NextVar(constsx)

        jump = {\
               And(fx < gH, sx < gH): \
               And(mfNext, msNext, fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               \
               And(fx < gH, sx >= gH): \
               And(mfNext, Not(msNext), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               \
               And(fx >= gH, sx < gH): \
               And(Not(mfNext), msNext, fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               \
               And(fx >= gH, sx >= gH): \
               And(Not(mfNext), Not(msNext), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx)}


        # STL propositions
        proZero = Bool('reachability')
        proBFL = Bool('bfonel')
        proF1 = Bool('fonef')
        proF2 = Bool('fones')
        proF3 = Bool('fonet')
        proF4 = Bool('fonefth')
        proTL = Bool('fthreep')
        proTR1 = Bool('fthreeqo')
        proTR2 = Bool('fthreeqt')
        proFiveR1 = Bool('ffiveqo')

        prop = {proZero: fx > RealVal(5.1), \
                proBFL: fx < RealVal(4.9), \
                proF1: fx > RealVal(0), proF2: fx <= RealVal(9), proF3: sx > RealVal(0), proF4: sx <= RealVal(9),\
                proTL: Not(mf), proTR1: mf, proTR2: fx > RealVal(5.5), \
                proFiveR1: ms} 

        super().__init__(vars, init, flow, inv, jump, prop, "QF_NRA")


