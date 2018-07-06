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

        fxOff = -K1 * ((RealVal(1) - c) * constfx + c * constsx) 
        fxOn = K2 * (h1 -((RealVal(1) - c) * constfx + c * constsx))
        sxOff = -K2 * ((RealVal(1) - c) * constsx + c * constfx)
        sxOn = K2 * (h2 -((RealVal(1) - c) * constsx + c * constfx))

        flow = {And(qf == qOff, qs == qOff): {fx: fxOff, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                   And(qf == qOff, qs == qOn): {fx: fxOff, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}, \
                   And(qf == qOn, qs == qOff): {fx: fxOn, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                   And(qf == qOn, qs == qOn): {fx: fxOn, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}}

        inv = {And(qf == qOff, qs == qOff): And(fx > RealVal(10), sx > RealVal(10)), \
                    And(qf == qOff, qs == qOn): And(fx > RealVal(10), sx < RealVal(30)), \
                    And(qf == qOn, qs == qOff): And(fx < RealVal(30), sx > RealVal(10)), \
                    And(qf == qOn, qs == qOn):  And(fx < RealVal(30), sx < RealVal(30))}

        jump = {And(fx > gT, sx > gT):  And(qfNext == qOff, qsNext == qOff, fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
                     And(fx <= gT, sx <= gT): And(qfNext == qOn, qsNext == qOn, fxNext == fx, constfxNext == fx, , sxNext == sx, constsxNext == sx), \
                     And(fx > gT, sx <= gT): And(qfNext == qOff, qsNext == qOn, fxNext == fx, sxNext == sx, constsxNext == sx, constfxNext == fx), \
                     And(fx <= gT, sx > gT): And(qfNext == qOn, qsNext == qOff, fxNext == fx, sxNext == sx, constfxNext == fx, constsxNext == sx)}

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












