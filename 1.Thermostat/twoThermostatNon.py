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
        fx = Real('x1')
        sx = Real('x2')
 
        modeNext = NextVar(m)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proMF = Bool('promf')

        proPS = Bool('ps')
        proQS = Bool('qs')
        proMS = Bool('proms')

        mode = {m: (1, 4)}
        vars = {fx: (-20, 100), sx: (-20, 100)}
        init = And(m == RealVal(4), fx >= gT - RealVal(1), fx <= gT + RealVal(1), sx >= gT - RealVal(1), sx <= gT + RealVal(1))

        fxOff = -K1 * ((RealVal(1) - RealVal(2) * c) * fx + c * sx) 
        fxOn = K1 * (h1 -((RealVal(1) -  RealVal(2) * c) * fx + c * sx))
        sxOff = -K2 * ((RealVal(1) -  RealVal(2) * c) * sx + c * fx) 
        sxOn = K2 * (h2 -((RealVal(1) -  RealVal(2) * c) * sx + c * fx))

        flow = {m == RealVal(4): {fx: fxOff, sx: sxOff}, \
                 m == RealVal(3): {fx: fxOff, sx: sxOn}, \
                   m == RealVal(2): {fx: fxOn, sx: sxOff}, \
                   m == RealVal(1): {fx: fxOn, sx: sxOn}}

        inv = {m == RealVal(4): And(fx > RealVal(10), sx > RealVal(10)), \
               m == RealVal(3): And(fx > RealVal(10), sx < RealVal(30)), \
               m == RealVal(2): And(fx < RealVal(30), sx > RealVal(10)), \
               m == RealVal(1):  And(fx < RealVal(30), sx < RealVal(30))}

        jump = {And(fx > gT, sx > gT):  And(modeNext == RealVal(4), sxNext == sx, fxNext == fx), \
                     And(fx <= gT, sx <= gT): And(modeNext == RealVal(1), fxNext == fx, sxNext == sx), \
                     And(fx > gT, sx <= gT): And(modeNext == RealVal(3), sxNext == sx, fxNext == fx), \
                     And(fx <= gT, sx > gT): And(modeNext == RealVal(2), sxNext == sx, fxNext == fx)}


        prop = {proPF: fx < gT - RealVal(1), (proQF): fx >  gT + RealVal(1), proMF: m == RealVal(4),  \
               proPS: sx < gT - RealVal(1), (proQS): sx >  gT + RealVal(1), proMS: m == RealVal(1)}

        goal = {m == RealVal(4): And(Or(fx > gT + RealVal(1), fx < gT - RealVal(1)), Or(sx > gT + RealVal(1), sx < gT - RealVal(1))), \
               m == RealVal(3): And(Or(fx > gT + RealVal(1), fx < gT - RealVal(1)), Or(sx > gT + RealVal(1), sx < gT - RealVal(1))), \
               m == RealVal(2): And(Or(fx > gT + RealVal(1), fx < gT - RealVal(1)), Or(sx > gT + RealVal(1), sx < gT - RealVal(1))), \
               m == RealVal(1): And(Or(fx > gT + RealVal(1), fx < gT - RealVal(1)), Or(sx > gT + RealVal(1), sx < gT - RealVal(1)))}

        super().__init__(mode, vars, init, flow, inv, jump, prop, 0.01, goal)


if __name__ == '__main__':
    model = Thermostat()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL() 












