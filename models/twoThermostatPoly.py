import os, sys
from stlMC import *
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
# STL
from .thermostatSTL import testcaseSTL

# reachability goal
#goal = Real('fx') > RealVal(23)
goal = Real('fx') < RealVal(16)
# some constants 
K1 = RealVal(0.015)
K2 = RealVal(0.045)
h1 = RealVal(100.00)
h2 = RealVal(200.00)
c = RealVal(0.01)

gT = RealVal(20)

class ThermostatPoly(Model):
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
        fxOff = -K1 * ((RealVal(1) - RealVal(2) * c) * constfx + c * constsx)
        fxOn = K1 * (h1 -((RealVal(1) - RealVal(2) * c) * constfx + c * constsx))
        sxOff = -K2 * ((RealVal(1) - RealVal(2) * c) * constsx + c * constfx)
        sxOn = K2 * (h2 -((RealVal(1) - RealVal(2) * c) * constsx + c * constfx))

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
        init = And(Not(mf), Not(ms), fx >= gT - RealVal(1), fx <= gT + RealVal(1), sx >= gT - RealVal(1), sx <= gT + RealVal(1), And(constfx == fx, constsx == sx))


        # set the interval bound to the variables
        vars = {fx: (-20, 100), sx: (-20, 100), constfx: (-20, 100), constsx: (-20, 100)}
        # invariant conditions
        inv = {And(Not(mf), Not(ms)): And(fx > RealVal(10), sx > RealVal(10)), \
               And(Not(mf), ms): And(fx > RealVal(10), sx < RealVal(30)), \
               And(mf, Not(ms)): And(fx < RealVal(30), sx > RealVal(10)), \
               And(mf, ms): And(fx < RealVal(30), sx < RealVal(30))}

        # jump conditions
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        constfxNext = NextVar(constfx)
        constsxNext = NextVar(constsx)

        jump = {\
                And(fx > gT, sx > gT): \
                And(Not(mfNext), Not(msNext), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
                \
                And(fx <= gT, sx <= gT): \
                And(mfNext, msNext, fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
                \
                And(fx > gT, sx <= gT): \
                And(Not(mfNext), msNext, fxNext == fx, sxNext == sx, constsxNext == sx, constfxNext == fx), \
                \
                And(fx <= gT, sx > gT): \
                And(mfNext, Not(msNext), fxNext == fx, sxNext == sx, constfxNext == fx, constsxNext == sx)}

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


        super().__init__(vars, init, flow, inv, jump, prop, "QF_NRA")
