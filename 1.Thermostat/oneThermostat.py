import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *

K1 = RealVal(0.015)
h1 = RealVal(100.0)
c = RealVal(0.01)

gT = RealVal(20)

class Thermostat(Model):
    def __init__(self):
        m = Real('mode')
        fx = Real('fx')
        constfx = Real('constfx')
        mNext = NextVar(m)
        fxNext = NextVar(fx)
        constfxNext = NextVar(constfx)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proMF = Bool('proMF')

        mode = {m: (1,2)}
        vars = {fx: (-20, 100), constfx: (-20, 100)}
        init = And(m == RealVal(2), fx >= gT - RealVal(1), fx <= gT + RealVal(1), constfx == fx)

        fxOff = -K1 * (RealVal(1) - RealVal(2) * c) * constfx 
        fxOn = K1 * (h1 -((RealVal(1) -  RealVal(2) * c) * constfx))

        flow = {m == RealVal(2): {fx: fxOff, constfx: RealVal(0)}, \
                m == RealVal(1): {fx: fxOn, constfx: RealVal(0)}}
        inv = {m == RealVal(2): fx > RealVal(10), \
               m == RealVal(1): fx < RealVal(30)}

        jump = {fx > gT: And(mNext == RealVal(1), fxNext == fx, constfxNext == fx), \
                fx <= gT: And(mNext == RealVal(2) , fxNext == fx, constfxNext == fx)}

        prop = {proPF: fx < gT - RealVal(1), (proQF): fx >  gT + RealVal(1), proMF: m == RealVal(4)}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Thermostat()
    const = model.reach(2)

    output = io.StringIO()
    printObject = dRealHandler(const, output, model.varList, model.variables, model.flowDict, model.mode)
    printObject.callAll()
    dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
    dRealname = dRealname[:-3]
    dRealname += '.smt2'
    f = open(dRealname, 'w')
    f.write(output.getvalue())
    f.close()
    s = z3.Solver()
    for i in range(len(const)):
        s.add(z3Obj(const[i]))
#    print(s.to_smt2())
#    print(s.check())

