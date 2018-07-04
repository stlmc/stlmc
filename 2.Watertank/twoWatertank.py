import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.interface import *
from core.dRealHandler import *
from model import *

gH = RealVal(5.0)
G = RealVal(9.806)
A1 = RealVal(8.0)
A2 = RealVal(9.0)
Q1 = RealVal(5.0)
Q2 = RealVal(3.0)
W = RealVal(0.5)


class Watertank(Model):
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

    def __init__(self):
        mode = [self.qf, self.qs]
        vars = {self.fx: (0, 10), self.sx: (0, 10), self.constfx: (0, 10), self.constsx: (0, 10)}
        init = And(And(self.qf == self.qOn, self.qs == self.qOn), self.fx >= gH - RealVal(0.1), self.fx <= gH + RealVal(0.1), self.sx >= gH - RealVal(0.1), self.sx <= gH + RealVal(0.1), And(self.constfx == self.fx, self.constsx == self.sx))

        fxOff = -W * Sqrt(RealVal(2) * G) * Sqrt(self.constfx) / A1 
        fxOn = (Q1 - W * Sqrt(RealVal(2) * G) * Sqrt(self.constfx)) / A1 
        sxOff = (W * Sqrt(RealVal(2) * G) * (Sqrt(self.constfx) - Sqrt(self.constsx))) / A2
        sxOn = (Q2 + W * Sqrt(RealVal(2) * G) * (Sqrt(self.constfx) - Sqrt(self.constsx))) / A2

        flow = {And(self.qf == self.qOff, self.qs == self.qOff): {self.fx: fxOff, self.sx: sxOff, self.constfx: RealVal(0), self.constsx: RealVal(0)}, \
                   And(self.qf == self.qOff, self.qs == self.qOn): {self.fx: fxOff, self.sx: sxOn, self.constfx: RealVal(0), self.constsx: RealVal(0)}, \
                   And(self.qf == self.qOn, self.qs == self.qOff): {self.fx: fxOn, self.sx: sxOff, self.constfx: RealVal(0), self.constsx: RealVal(0)}, \
                   And(self.qf == self.qOn, self.qs == self.qOn): {self.fx: fxOn, self.sx: sxOn, self.constfx: RealVal(0), self.constsx: RealVal(0)}}

        inv = {And(self.qf == self.qOff, self.qs == self.qOff): And(self.fx > RealVal(0), self.sx > RealVal(0)), \
                    And(self.qf == self.qOff, self.qs == self.qOn): And(self.fx > RealVal(0), self.sx <= A2), \
                    And(self.qf == self.qOn, self.qs == self.qOff): And(self.fx <= A1, self.sx > RealVal(0) ), \
                    And(self.qf == self.qOn, self.qs == self.qOn):  And(self.fx <= A1, self.sx <= A2)}

        jump = {And(self.fx < gH, self.sx < gH):  And(self.qfNext == self.qOn, self.qsNext == self.qOn, self.fxNext == self.fx, self.constfxNext == self.fx, self.sxNext == self.sx, self.constsxNext == self.sx), \
               And(self.fx < gH, self.sx >= gH):  And(self.qfNext == self.qOn, self.qsNext == self.qOff, self.fxNext == self.fx, self.constfxNext == self.fx, self.sxNext == self.sx, self.constsxNext == self.sx), \
               And(self.fx >= gH, self.sx < gH):  And(self.qfNext == self.qOff, self.qsNext == self.qOn, self.fxNext == self.fx, self.constfxNext == self.fx, self.sxNext == self.sx, self.constsxNext == self.sx), \
               And(self.fx >= gH, self.sx >= gH):  And(self.qfNext == self.qOff, self.qsNext == self.qOff, self.fxNext == self.fx, self.constfxNext == self.fx, self.sxNext == self.sx, self.constsxNext == self.sx)}


        prop = {self.proPF: self.fx >= RealVal(2), (self.proQF): self.fx <=  RealVal(5)}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Watertank()
    const = model.reach(4)

    output = io.StringIO()
    printObject = dRealHandler(const, output, model.variables, model.flowDict)
    printObject.callAll()
#    print (output.getvalue())
    dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
    dRealname = dRealname[:-3]
    dRealname += '.smt2'
    f = open(dRealname, 'w')
    f.write(output.getvalue())
    f.close()
    s = z3.Solver()
    for i in range(len(const)):
        s.add(const[i].z3Obj())
#    print(s.to_smt2())
    print(s.check())













