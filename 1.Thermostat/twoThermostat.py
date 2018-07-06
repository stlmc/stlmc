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

        mode = [qf, qs]
        vars = {fx: (-20, 100), sx: (-20, 100), constfx: (-20, 100), constsx: (-20, 100)}
        init = And(And(qf == qOff, qs == qOff), fx >= gT - RealVal(1), fx <= gT + RealVal(1), sx >= gT - RealVal(1), sx <= gT + RealVal(1), And(constfx == fx, constsx == sx))

        fxOff = -S1 * (constfx - (D1 * constsx))
        fxOn = S1 * (H1 -(constfx - (D1 * constsx)))
        sxOff = -S2 * (constsx -D1 * constfx)
        sxOn = S2 * (H2 - (constsx - D1 * constfx))

        flow = {And(qf == qOff, qs == qOff): {fx: fxOff, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                   And(qf == qOff, qs == qOn): {fx: fxOff, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}, \
                   And(qf == qOn, qs == qOff): {fx: fxOn, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                   And(qf == qOn, qs == qOn): {fx: fxOn, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}}

        inv = {And(qf == qOff, qs == qOff): And(fx > RealVal(10), sx > RealVal(10)), \
                    And(qf == qOff, qs == qOn): And(fx > RealVal(10), sx < RealVal(30)), \
                    And(qf == qOn, qs == qOff): And(fx < RealVal(30), sx > RealVal(10)), \
                    And(qf == qOn, qs == qOn):  And(fx < RealVal(30), sx < RealVal(30))}

        jump = {And(qf == qOn, fx > UB):  And(qfNext == qOff, fxNext == fx, constfxNext == fx), \
                     And(qf == qOff, fx < LB): And(qfNext == qOn, fxNext == fx, constfxNext == fx), \
                     And(LB <= fx, fx <= UB): And(qfNext == qf, fxNext == fx, constfxNext == fx), \
                     And(qs == qOn, sx > UB): And(qsNext == qOff, sxNext == sx, constsxNext == sx), \
                     And(qs == qOff, sx < LB): And(qsNext == qOn, sxNext == sx, constsxNext == sx), \
                     And(sx >= LB, sx <= UB): And(qsNext == qs, sxNext == sx, constsxNext == sx)}


        prop = {proPF: fx >= RealVal(10), (proQF): fx <=  RealVal(10)}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Thermostat()
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
    try:
        s = z3.Solver()
        for c in const:
            s.add(z3Obj(c))
#        print(s.to_smt2())
        print(s.check())
    except z3constODEerror:
        print("receive nonlinear ODE")












