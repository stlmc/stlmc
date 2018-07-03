from core.interface import *
import os, sys
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
    qOn  = BoolVal(True)
    qOff = BoolVal(False)
    qf = Bool('mf')
    qs = Bool('ms')
    fx = Real('fx')
    sx = Real('sx')
    constfx = Real('constfx')
    constsx = Real('constsx')
    qfNext = NextVar(qf)
    qsNext = NextVar(qs)
    fxNext = NextVar(fx)
    sxNext = NextVar(sx)
    constfxNext = NextVar(constfx)
    constsxNext = NextVar(constsx)
    proPF = Bool('pf')
    proQF = Bool('qf')

    def reach(self, bound):
        self.mode = [self.qf, self.qs]
        self.vars = {self.fx: (-20, 100), self.sx: (-20, 100), self.constfx: (-20, 100), self.constsx: (-20, 100)}
        self.init = And(And(self.qf == self.qOff, self.qs == self.qOff), self.fx >= gT - RealVal(1), self.fx <= gT + RealVal(1), self.sx >= gT - RealVal(1), self.sx <= gT + RealVal(1), And(self.constfx == self.fx, self.constsx == self.sx))

        fxOff = -S1 * (self.constfx - (D1 * self.constsx))
        fxOn = S1 * (H1 -(self.constfx - (D1 * self.constsx)))
        sxOff = -S2 * (self.constsx -D1 * self.constfx)
        sxOn = S2 * (H2 - (self.constsx - D1 * self.constfx))

        self.flow = {And(self.qf == self.qOff, self.qs == self.qOff): {self.fx: fxOff, self.sx: sxOff, self.constfx: RealVal(0), self.constsx: RealVal(0)}, \
                   And(self.qf == self.qOff, self.qs == self.qOn): {self.fx: fxOff, self.sx: sxOn, self.constfx: RealVal(0), self.constsx: RealVal(0)}, \
                   And(self.qf == self.qOn, self.qs == self.qOff): {self.fx: fxOn, self.sx: sxOff, self.constfx: RealVal(0), self.constsx: RealVal(0)}, \
                   And(self.qf == self.qOn, self.qs == self.qOn): {self.fx: fxOn, self.sx: sxOn, self.constfx: RealVal(0), self.constsx: RealVal(0)}}

        self.inv = {And(self.qf == self.qOff, self.qs == self.qOff): And(self.fx > RealVal(10), self.sx > RealVal(10)), \
                    And(self.qf == self.qOff, self.qs == self.qOn): And(self.fx > RealVal(10), self.sx < RealVal(30)), \
                    And(self.qf == self.qOn, self.qs == self.qOff): And(self.fx < RealVal(30), self.sx > RealVal(10)), \
                    And(self.qf == self.qOn, self.qs == self.qOn):  And(self.fx < RealVal(30), self.sx < RealVal(30))}
        '''
        self.jump = [And(self.qf == self.qOn, self.fx > UB, self.qfNext == self.qOff, self.fxNext == self.fx, self.constfxNext == self.fx), \
                     And(self.qf == self.qOff, self.fx < LB, self.qfNext == self.qOn, self.fxNext == self.fx, self.constfxNext == self.fx), \
                     And(LB <= self.fx, self.fx <= UB, self.qfNext == self.qf, self.fxNext == self.fx, self.constfxNext == self.fx), \
                     And(self.qs == self.qOn, self.sx > UB, self.qsNext == self.qOff, self.sxNext == self.sx, self.constsxNext == self.sx), \
                     And(self.qs == self.qOff, self.sx < LB, self.qsNext == self.qOn, self.sxNext == self.sx, self.constsxNext == self.sx), \
                     And(self.sx >= LB, self.sx <= UB, self.qsNext == self.qs, self.sxNext == self.sx, self.constsxNext == self.sx)]
        '''
        self.jump = {And(self.qf == self.qOn, self.fx > UB, self.qfNext == self.qOff): And(self.fxNext == self.fx, self.constfxNext == self.fx), \
                     And(self.qf == self.qOff, self.fx < LB, self.qfNext == self.qOn): And(self.fxNext == self.fx, self.constfxNext == self.fx), \
                     And(LB <= self.fx, self.fx <= UB): And(self.qfNext == self.qf, self.fxNext == self.fx, self.constfxNext == self.fx), \
                     And(self.qs == self.qOn, self.sx > UB): And(self.qsNext == self.qOff, self.sxNext == self.sx, self.constsxNext == self.sx), \
                     And(self.qs == self.qOff, self.sx < LB): And(self.qsNext == self.qOn, self.sxNext == self.sx, self.constsxNext == self.sx), \
                     And(self.sx >= LB, self.sx <= UB): And(self.qsNext == self.qs, self.sxNext == self.sx, self.constsxNext == self.sx)}


        self.prop = {self.proPF: self.fx >= RealVal(20), (self.proQF): self.fx <=  RealVal(17)}
       
        (const, printObject) = Model().making(self.mode, self.vars, self.init, self.flow, self.inv, self.jump, self.prop, bound, 'TwoThermostat.smt2')

        return const

if __name__ == '__main__':
    const = Thermostat().reach(4)
    s = z3.Solver()
    for i in range(len(const)):
        s.add(const[i].z3Obj())
#    print(s.to_smt2())
#    print(s.check())













