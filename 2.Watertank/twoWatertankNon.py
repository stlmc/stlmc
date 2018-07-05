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
    def __init__(self):
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


        mode = [qf, qs]
        vars = {fx: (0, 10), sx: (0, 10)}
        init = And(And(qf == qOn, qs == qOn), fx >= gH - RealVal(0.1), fx <= gH + RealVal(0.1), sx >= gH - RealVal(0.1), sx <= gH + RealVal(0.1))

        fxOff = -W * Sqrt(RealVal(2) * G) * Sqrt(fx) / A1 
        fxOn = (Q1 - W * Sqrt(RealVal(2) * G) * Sqrt(fx)) / A1 
        sxOff = (W * Sqrt(RealVal(2) * G) * (Sqrt(fx) - Sqrt(sx))) / A2
        sxOn = (Q2 + W * Sqrt(RealVal(2) * G) * (Sqrt(fx) - Sqrt(sx))) / A2

        flow = {And(qf == qOff, qs == qOff): {fx: fxOff, sx: sxOff}, \
                   And(qf == qOff, qs == qOn): {fx: fxOff, sx: sxOn}, \
                   And(qf == qOn, qs == qOff): {fx: fxOn, sx: sxOff}, \
                   And(qf == qOn, qs == qOn): {fx: fxOn, sx: sxOn}}

        inv = {And(qf == qOff, qs == qOff): And(fx > RealVal(0), sx > RealVal(0)), \
                    And(qf == qOff, qs == qOn): And(fx > RealVal(0), sx <= A2), \
                    And(qf == qOn, qs == qOff): And(fx <= A1, sx > RealVal(0) ), \
                    And(qf == qOn, qs == qOn):  And(fx <= A1, sx <= A2)}

        jump = {And(fx < gH, sx < gH):  And(qfNext == qOn, qsNext == qOn, fxNext == fx, sxNext == sx), \
               And(fx < gH, sx >= gH):  And(qfNext == qOn, qsNext == qOff, fxNext == fx, sxNext == sx), \
               And(fx >= gH, sx < gH):  And(qfNext == qOff, qsNext == qOn, fxNext == fx, sxNext == sx), \
               And(fx >= gH, sx >= gH):  And(qfNext == qOff, qsNext == qOff, fxNext == fx, sxNext == sx)} 


        prop = {proPF: fx >= RealVal(1), (proQF): qf == qOn}

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
    try:
        s = z3.Solver()
        for i in range(len(const)):
            s.add(const[i].z3Obj())
#        print(s.to_smt2())
        print(s.check())
    except z3constODEerror:
        print("receive nonlinear ODE")












