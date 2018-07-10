import os, sys, io
from tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
from core.STLHandler import *

gH = RealVal(5.0)
g = RealVal(9.806)
a = RealVal(0.5)

A1 = RealVal(8.0)
A2 = RealVal(9.0)
q1 = RealVal(5.0)
q2 = RealVal(3.0)

class Watertank(Model):
    def __init__(self):
        m  = Real('mode')
        fx = Real('fx')
        sx = Real('sx')
        constfx = Real('constfx')
        constsx = Real('constsx')

        mNext = NextVar(m)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        constfxNext = NextVar(constfx)
        constsxNext = NextVar(constsx)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proMF1 = Bool('promf1')
        proMF2 = Bool('promf2')
        proZF = Bool('zf')

        mode = {m: (1, 4)}
        vars = {fx: (0, 10), sx: (0, 10), constfx: (0, 10), constsx: (0, 10)}
        init = And(m == RealVal(1), fx >= gH - RealVal(0.1), fx <= gH + RealVal(0.1), sx >= gH - RealVal(0.1), sx <= gH + RealVal(0.1), And(constfx == fx, constsx == sx))

        fxOff = -a * Sqrt(RealVal(2) * g) * constfx / (RealVal(2) * A1) 
        fxOn = (q1 - a * Sqrt(RealVal(2) * g) * constfx) / (RealVal(2) * A1)
        sxOff = (a * Sqrt(RealVal(2) * g) * (constfx - constsx)) / (RealVal(2) * A2)
        sxOn = (q2 + a * Sqrt(RealVal(2) * g) * (constfx - constsx)) / (RealVal(2) * A2)

        flow = {m == RealVal(4): {fx: fxOff, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                m == RealVal(3): {fx: fxOff, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}, \
                m == RealVal(2): {fx: fxOn, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                m == RealVal(1): {fx: fxOn, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}}

        inv = {m == RealVal(4): And(fx > RealVal(0), sx > RealVal(0)), \
               m == RealVal(3): And(fx > RealVal(0), sx <= A2), \
               m == RealVal(2): And(fx <= A1, sx > RealVal(0) ), \
               m == RealVal(1):  And(fx <= A1, sx <= A2)}

        jump = {And(fx < gH, sx < gH):  And(mNext == RealVal(1), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               And(fx < gH, sx >= gH):  And(mNext == RealVal(2), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               And(fx >= gH, sx < gH):  And(mNext == RealVal(3), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               And(fx >= gH, sx >= gH):  And(mNext == RealVal(4), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx)}

        prop = {proPF: fx <= A1, (proQF): fx < RealVal(5), (proMF1): m == RealVal(1), proMF2: m == RealVal(2), proZF: fx > RealVal(6) }

        super().__init__(mode, vars, init, flow, inv, jump, prop, 0.1)


if __name__ == '__main__':
    model = Watertank()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()












