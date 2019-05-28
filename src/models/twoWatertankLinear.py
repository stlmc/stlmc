import os, sys
from stlMC import *
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))

# STL
from .watertankSTL import testcaseSTL

# reachability goal
goal = Real('sx') > RealVal(5.5) 

# some constants 
gH = RealVal(5.0)
L = RealVal(1.0)

class WatertankLinear(Model):
    def __init__(self):
        # modes
        mf = Bool('mf')
        ms = Bool('ms')

        # variables
        fx = Real('fx')
        sx = Real('sx')

        # flow conditions
        fxOff = -RealVal(0.2) 
        fxOn = RealVal(0.5)
        sxOff = -RealVal(0.3)
        sxOn = RealVal(0.6)

        flow = {And(Not(mf), Not(ms)): {fx: fxOff, sx: sxOff}, \
                And(Not(mf), ms): {fx: fxOff, sx: sxOn}, \
                And(mf, Not(ms)): {fx: fxOn, sx: sxOff}, \
                And(mf, ms): {fx: fxOn, sx: sxOn}}

        # initial conditions
        init = And(mf, ms, fx >= gH - RealVal(0.1), fx <= gH + RealVal(0.1), sx >= gH - RealVal(0.1), sx <= gH + RealVal(0.1))


        # set the interval bound to the variables
        vars = {fx: (0, 10), sx: (0, 10)}
        # invariant conditions
        inv = {And(Not(mf), Not(ms)): And(fx > RealVal(0), sx > RealVal(0)), \
               And(Not(mf), ms): And(fx > RealVal(0), sx < RealVal(8)), \
               And(mf, Not(ms)): And(fx < RealVal(8), sx > RealVal(0) ), \
               And(mf, ms):  And(fx < RealVal(8), sx < RealVal(8))}


        # jump conditions
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)

        jump = {And(fx < L, sx < L):  And(mfNext, msNext, fxNext == fx, sxNext == sx), \
               And(fx < L, sx >= L):  And(mfNext, Not(msNext), fxNext == fx, sxNext == sx), \
               And(fx >= (L - sx), sx < L):  And(Not(mfNext), msNext, fxNext == fx, sxNext == sx), \
               And(fx >= (sx - L), sx >= L):  And(Not(mfNext), Not(msNext), fxNext == fx, sxNext == sx)}


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

        super().__init__(vars, init, flow, inv, jump, prop, "QF_LRA")

