import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *

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
 
        modeNext = NextVar(m)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proMF = Bool('proMF')

        proPS = Bool('ps')
        proQS = Bool('qs')
        proMS = Bool('proMS')

        mode = {m: (1, 4)}
        vars = {fx: (-20, 100), sx: (-20, 100)}
        init = And(m == RealVal(4), fx >= gT - RealVal(1), fx <= gT + RealVal(1), sx >= gT - RealVal(1), sx <= gT + RealVal(1))

        fxOff = -K1 * ((RealVal(1) - c) * fx + c * sx) 
        fxOn = K2 * (h1 -((RealVal(1) - c) * fx + c * sx))
        sxOff = -K2 * ((RealVal(1) - c) * sx + c * fx) 
        sxOn = K2 * (h2 -((RealVal(1) - c) * sx + c * fx))

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
               proPS: sx < gT - RealVal(1), (proQS): sx >  gT + RealVal(1), proMS: m == RealVal(4)}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Thermostat()
    const = model.reach(5)

    output = io.StringIO()
    printObject = dRealHandler(const, output, model.varList, model.variables, model.flowDict, model.mode)
    printObject.callAll()
#    print (output.getvalue())
    dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
    dRealname = dRealname[:-3]
    dRealname += '.smt2'
    f = open(dRealname, 'w')
    f.write(output.getvalue())
    f.close()












