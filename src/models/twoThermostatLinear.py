import os, sys
from stlMC import *
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))

# STL
from .thermostatSTL import testcaseSTL

# reachability goal
#goal = Real('fx') > RealVal(23)
goal = Real('fx') < RealVal(17)
# some constants 
gT = RealVal(20)

class ThermostatLinear(Model):
    def __init__(self):
        # modes
        mf = Bool('mf')
        ms = Bool('ms')

        # variables
        fx = Real('fx')
        sx = Real('sx')

        # flow conditions
        fxOff = -RealVal(0.4) 
        fxOn = RealVal(0.7)
        sxOff = -RealVal(0.6)
        sxOn = RealVal(1)

        flow = {\
                And(Not(mf), Not(ms)): {fx: fxOff, sx: sxOff}, \
                \
                And(Not(mf), ms): {fx: fxOff, sx: sxOn}, \
                \
                And(mf, Not(ms)): {fx: fxOn, sx: sxOff}, \
                \
                And(mf, ms): {fx: fxOn, sx: sxOn}}

        # initial conditions
        init = And(Not(mf), Not(ms), fx >= gT - RealVal(0.1), fx <= gT + RealVal(0.1), sx >= gT + RealVal(3), sx <= gT + RealVal(3.5))

        # set the interval bound to the variables 
        vars = {fx: (-20, 100), sx: (-20, 100)}
        # invariant conditions
        inv = {And(Not(mf), Not(ms)): And(fx > RealVal(0), sx > RealVal(0)), \
               And(Not(mf), ms): And(fx > RealVal(0), sx < RealVal(50)), \
               And(mf, Not(ms)): And(fx < RealVal(50), sx > RealVal(0)), \
               And(mf, ms):  And(fx < RealVal(50), sx < RealVal(50))}

        # jump conditions
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)

        jump = {\
                And((fx > ((fx + sx) / RealVal(2))), (sx > ((fx + sx) / RealVal(2)))):  \
                And(Not(mfNext), Not(msNext), fxNext == fx, sxNext == sx), \
                \
                And((fx <= ((fx + sx) / RealVal(2))), (sx <= ((fx + sx) / RealVal(2)))): \
                And(mfNext, msNext, fxNext == fx, sxNext == sx), \
                \
                And((fx > ((fx + sx) / RealVal(2))), (sx <= ((fx + sx) / RealVal(2)))): \
                And(Not(mfNext),msNext, fxNext == fx, sxNext == sx), \
                \
                And((fx <= ((fx + sx) / RealVal(2))), (sx > ((fx + sx) / RealVal(2)))): \
                And(mfNext, Not(msNext), fxNext == fx, sxNext == sx)}


        # STL propositions
        proZero = Bool('reachability')
        proFL1 = Bool('fonepo')
        proFL2 = Bool('fonept')
        proFR = Bool('foneq')
        proSL1 = Bool('ftwopo')
        proSL2 = Bool('ftwopt')
        proFour1 = Bool('ffourpo')
        proFour2 = Bool('ffourpt')

        prop = {proZero: fx > RealVal(21), \
               proFL1: mf, proFL2: ms, proFR: (sx <= RealVal(20)), \
               proSL1: Not(mf), proSL2: Not(ms), \
               proFour1: (fx < RealVal(30)), \
               proFour2: (fx > RealVal(10))}


        super().__init__(vars, init, flow, inv, jump, prop, "QF_LRA")

