import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *

gT = RealVal(20)
LB = RealVal(16)
UB = RealVal(24)
MAX = RealVal(30)
MIN = RealVal(10)
S1 = RealVal(5)
S2 = RealVal(7)
S3 = RealVal(6)
H1 = RealVal(3)
H2 = RealVal(5)
H3 = RealVal(2)
D1 = RealVal(2)
D2 = RealVal(2)

class Thermostat(Model):
    def __init__(self):
        qOn  = BoolVal(True)
        qOff = BoolVal(False)
        qf = Bool('mf')
        fx = Real('fx')
        constfx = Real('constfx')
        qfNext = NextVar(qf)
        fxNext = NextVar(fx)
        constfxNext = NextVar(constfx)
        proPF = Bool('pf')
        proQF = Bool('qf')

        mode = [qf]
        vars = {fx: (-20, 100), constfx: (-20, 100)}
        init = And(qf == qOff, fx >= gT - RealVal(1), fx <= gT + RealVal(1), constfx == fx)

        fxOff = -S1 * (constfx)
        fxOn = S1 * (H1 -constfx)

        flow = {qf == qOff: {fx: fxOff, constfx: RealVal(0)}, \
                qf == qOn: {fx: fxOn, constfx: RealVal(0)}}
        inv = {qf == qOff: fx > RealVal(10), \
               qf == qOn: fx < RealVal(30)}

        jump = {And(qf == qOn, fx > UB): And(qfNext == qOff, fxNext == fx, constfxNext == fx), \
                     And(qf == qOff, fx < LB): And(qfNext == qOn, fxNext == fx, constfxNext == fx), \
                     And(LB <= fx, fx <= UB): And(qfNext == qf, fxNext == fx, constfxNext == fx)}

        prop = {proPF: fx <= RealVal(5), (proQF): fx <= RealVal(0)}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Thermostat()
    const = model.reach(2)

    output = io.StringIO()
    printObject = dRealHandler(const, output, model.variables, model.flowDict)
    printObject.callAll()
    f = open('test.smt2', 'w')
    f.write(output.getvalue())
    f.close()

    s = z3.Solver()
    for i in range(len(const)):
        s.add(z3Obj(const[i]))
#    print(s.to_smt2())
    print(s.check())

