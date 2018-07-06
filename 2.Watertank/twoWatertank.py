import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *

gH = RealVal(5.0)
g = RealVal(9.806)
a = RealVal(0.5)

A1 = RealVal(2.0)
A2 = RealVal(4.0)
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

        mode = {m: (1, 4)}
        vars = {fx: (0, 10), sx: (0, 10), constfx: (0, 10), constsx: (0, 10)}
        init = And(m == RealVal(1), fx >= gH - RealVal(0.1), fx <= gH + RealVal(0.1), sx >= gH - RealVal(0.1), sx <= gH + RealVal(0.1), And(constfx == fx, constsx == sx))

        fxOff = -a * Sqrt(RealVal(2) * g) * Sqrt(constfx) / A1 
        fxOn = (q1 - a * Sqrt(RealVal(2) * g) * Sqrt(constfx)) / A1
        sxOff = (a * Sqrt(RealVal(2) * g) * (Sqrt(constfx) - Sqrt(constsx))) / A2
        sxOn = (q2 + a * Sqrt(RealVal(2) * g) * (Sqrt(constfx) - Sqrt(constsx))) / A2

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


        prop = {proPF: fx >= RealVal(2), (proQF): fx <=  RealVal(5)}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Watertank()
    const = model.reach(4)

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
    s = z3.Solver()
    for c in const:
        s.add(z3Obj(c))
#    print(s.to_smt2())
    print(s.check())













