from core.interface import *
from core.dRealHandler import *
from model import *
import os, sys, io

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

    def __init__(self):
        mode = [self.qf]
        vars = {self.fx: (-20, 100), self.constfx: (-20, 100)}
        init = And(self.qf == self.qOff, self.fx >= gT - RealVal(1), self.fx <= gT + RealVal(1), self.constfx == self.fx)

        fxOff = -S1 * (self.constfx)
        fxOn = S1 * (H1 -self.constfx)

        flow = {self.qf == self.qOff: {self.fx: fxOff, self.constfx: RealVal(0)}, \
                self.qf == self.qOn: {self.fx: fxOn, self.constfx: RealVal(0)}}
        inv = {self.qf == self.qOff: self.fx > RealVal(10), \
               self.qf == self.qOn: self.fx < RealVal(30)}

        jump = {And(self.qf == self.qOn, self.fx > UB): And(self.qfNext == self.qOff, self.fxNext == self.fx, self.constfxNext == self.fx), \
                     And(self.qf == self.qOff, self.fx < LB): And(self.qfNext == self.qOn, self.fxNext == self.fx, self.constfxNext == self.fx), \
                     And(LB <= self.fx, self.fx <= UB): And(self.qfNext == self.qf, self.fxNext == self.fx, self.constfxNext == self.fx)}

        prop = {self.proPF: self.fx >= RealVal(20), (self.proQF): self.qf == self.qOn}

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
        s.add(const[i].z3Obj())
#    print(s.to_smt2())
    print(s.check())

