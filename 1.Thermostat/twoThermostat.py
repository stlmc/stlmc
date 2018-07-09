import os, sys, io
from tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
from core.STLHandler import *


K1 = RealVal(0.015)
K2 = RealVal(0.045)
h1 = RealVal(100.0)
h2 = RealVal(200.0)
c = RealVal(0.01)

gT = RealVal(20)

class Thermostat(Model):
    def __init__(self):
        m = Real('mode')
        fx = Real('fx')
        sx = Real('sx')
        constfx = Real('constfx')
        constsx = Real('constsx')

        modeNext = NextVar(m)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        constfxNext = NextVar(constfx)
        constsxNext = NextVar(constsx)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proMF = Bool('proMF')

        proPS = Bool('ps')
        proQS = Bool('qs')
        proMS = Bool('proMS')

        mode = {m: (1, 4)}
        vars = {fx: (-20, 100), sx: (-20, 100), constfx: (-20, 100), constsx: (-20, 100)}
        init = And(m == RealVal(4), fx >= gT - RealVal(1), fx <= gT + RealVal(1), sx >= gT - RealVal(1), sx <= gT + RealVal(1), And(constfx == fx, constsx == sx))

        fxOff = -K1 * ((RealVal(1) - RealVal(2) * c) * constfx + c * constsx) 
        fxOn = K1 * (h1 -((RealVal(1) - RealVal(2) * c) * constfx + c * constsx))
        sxOff = -K2 * ((RealVal(1) - RealVal(2) * c) * constsx + c * constfx)
        sxOn = K2 * (h2 -((RealVal(1) - RealVal(2) * c) * constsx + c * constfx))

        flow = {m == RealVal(4): {fx: fxOff, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                m == RealVal(3): {fx: fxOff, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}, \
                m == RealVal(2): {fx: fxOn, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                m == RealVal(1): {fx: fxOn, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}}

        inv = {m == RealVal(4): And(fx > RealVal(10), sx > RealVal(10)), \
               m == RealVal(3): And(fx > RealVal(10), sx < RealVal(30)), \
               m == RealVal(2): And(fx < RealVal(30), sx > RealVal(10)), \
               m == RealVal(1):  And(fx < RealVal(30), sx < RealVal(30))}

        jump = {And(fx > gT, sx > gT):  And(modeNext == RealVal(4), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
                     And(fx <= gT, sx <= gT): And(modeNext == RealVal(1), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
                     And(fx > gT, sx <= gT): And(modeNext == RealVal(3), fxNext == fx, sxNext == sx, constsxNext == sx, constfxNext == fx), \
                     And(fx <= gT, sx > gT): And(modeNext == RealVal(2), fxNext == fx, sxNext == sx, constfxNext == fx, constsxNext == sx)}

        prop = {proPF: fx < gT - RealVal(1), (proQF): fx >  gT + RealVal(1), proMF: m == RealVal(4), \
               proPS: sx < gT - RealVal(1), (proQS): sx >  gT + RealVal(1), proMS: m == RealVal(1)}

        super().__init__(mode, vars, init, flow, inv, jump, prop, 1)


if __name__ == '__main__':
    model = Thermostat()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()












