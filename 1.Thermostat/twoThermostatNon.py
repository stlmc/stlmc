import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.interface import *
from core.dRealHandler import *
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
    qfNext = NextVar(qf)
    qsNext = NextVar(qs)
    fxNext = NextVar(fx)
    sxNext = NextVar(sx)
    proPF = Bool('pf')
    proQF = Bool('qf')

    def __init__(self):
        mode = [self.qf, self.qs]
        vars = {self.fx: (-20, 100), self.sx: (-20, 100)}
        init = And(And(self.qf == self.qOff, self.qs == self.qOff), self.fx >= gT - RealVal(1), self.fx <= gT + RealVal(1), self.sx >= gT - RealVal(1), self.sx <= gT + RealVal(1))

        fxOff = -S1 * (self.fx - (D1 * self.sx))
        fxOn = S1 * (H1 -(self.fx - (D1 * self.sx)))
        sxOff = -S2 * (self.sx -D1 * self.fx)
        sxOn = S2 * (H2 - (self.sx - D1 * self.fx))

        flow = {And(self.qf == self.qOff, self.qs == self.qOff): {self.fx: fxOff, self.sx: sxOff}, \
                   And(self.qf == self.qOff, self.qs == self.qOn): {self.fx: fxOff, self.sx: sxOn}, \
                   And(self.qf == self.qOn, self.qs == self.qOff): {self.fx: fxOn, self.sx: sxOff}, \
                   And(self.qf == self.qOn, self.qs == self.qOn): {self.fx: fxOn, self.sx: sxOn}}

        inv = {And(self.qf == self.qOff, self.qs == self.qOff): And(self.fx > RealVal(10), self.sx > RealVal(10)), \
                    And(self.qf == self.qOff, self.qs == self.qOn): And(self.fx > RealVal(10), self.sx < RealVal(30)), \
                    And(self.qf == self.qOn, self.qs == self.qOff): And(self.fx < RealVal(30), self.sx > RealVal(10)), \
                    And(self.qf == self.qOn, self.qs == self.qOn):  And(self.fx < RealVal(30), self.sx < RealVal(30))}

        jump = {And(self.qf == self.qOn, self.fx > UB):  And(self.qfNext == self.qOff, self.fxNext == self.fx), \
                     And(self.qf == self.qOff, self.fx < LB): And(self.qfNext == self.qOn, self.fxNext == self.fx), \
                     And(LB <= self.fx, self.fx <= UB): And(self.qfNext == self.qf, self.fxNext == self.fx), \
                     And(self.qs == self.qOn, self.sx > UB): And(self.qsNext == self.qOff, self.sxNext == self.sx), \
                     And(self.qs == self.qOff, self.sx < LB): And(self.qsNext == self.qOn, self.sxNext == self.sx), \
                     And(self.sx >= LB, self.sx <= UB): And(self.qsNext == self.qs, self.sxNext == self.sx)}


        prop = {self.proPF: self.fx >= RealVal(10), (self.proQF): self.fx <=  RealVal(10)}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Thermostat()
    const = model.reach(2)

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
    try:
        s = z3.Solver()
        for i in range(len(const)):
            s.add(const[i].z3Obj())
#        print(s.to_smt2())
        print(s.check())
    except z3constODEerror:
        print("receive nonlinear ODE")












