import os, sys, io
from tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
from core.STLHandler import *

gH = RealVal(5.0)
g = RealVal(9.80665)
a = RealVal(0.5)

A1 = RealVal(2.0)
A2 = RealVal(3.0)
q1 = RealVal(5.0)
q2 = RealVal(3.0)

class Watertank(Model):
    def __init__(self):
        m  = Real('mode')
        fx = Real('x1')
        sx = Real('x2')
        mNext = NextVar(m)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proZF = Bool('zf')
        proMF1 = Bool('promf1')
        proMF2 = Bool('promf2')

        mode = {m: (1, 4)}
        vars = {fx: (0, 10), sx: (0, 10)}
        init = And(m == RealVal(1), fx >= gH - RealVal(0.1), fx <= gH + RealVal(0.1), sx >= gH - RealVal(0.1), sx <= gH + RealVal(0.1))

        fxOff = -a * Sqrt(RealVal(2) * g) * Sqrt(fx) / A1 
        fxOn = (q1 - a * Sqrt(RealVal(2) * g) * Sqrt(fx)) / A1 
        sxOff = (a * Sqrt(RealVal(2) * g) * (Sqrt(fx) - Sqrt(sx))) / A2
        sxOn = (q2 + a * Sqrt(RealVal(2) * g) * (Sqrt(fx) - Sqrt(sx))) / A2

        flow = {m == RealVal(4): {fx: fxOff, sx: sxOff}, \
                m == RealVal(3): {fx: fxOff, sx: sxOn}, \
                m == RealVal(2): {fx: fxOn, sx: sxOff}, \
                m == RealVal(1): {fx: fxOn, sx: sxOn}}

        inv = {m == RealVal(4): And(fx > RealVal(0), sx > RealVal(0)), \
               m == RealVal(3): And(fx > RealVal(0), sx <= RealVal(9)), \
               m == RealVal(2): And(fx <= RealVal(9), sx > RealVal(0) ), \
               m == RealVal(1):  And(fx <= RealVal(9), sx <= RealVal(9))}

        jump = {And(fx < gH, sx < gH):  And(mNext == RealVal(1), fxNext == fx, sxNext == sx), \
               And(fx < gH, sx >= gH):  And(mNext == RealVal(2), fxNext == fx, sxNext == sx), \
               And(fx >= gH, sx < gH):  And(mNext == RealVal(3), fxNext == fx, sxNext == sx), \
               And(fx >= gH, sx >= gH):  And(mNext == RealVal(4), fxNext == fx, sxNext == sx)} 

        goal = {m == RealVal(4): And(Or(fx > gH + RealVal(0.1), fx < gH - RealVal(0.1)), Or(sx > gH + RealVal(0.1), sx < gH - RealVal(0.1))), \
               m == RealVal(3): And(Or(fx > gH + RealVal(0.1), fx < gH - RealVal(0.1)), Or(sx > gH + RealVal(0.1), sx < gH - RealVal(0.1))), \
               m == RealVal(2): And(Or(fx > gH + RealVal(0.1), fx < gH - RealVal(0.1)), Or(sx > gH + RealVal(0.1), sx < gH - RealVal(0.1))), \
               m == RealVal(1): And(Or(fx > gH + RealVal(0.1), fx < gH - RealVal(0.1)), Or(sx > gH + RealVal(0.1), sx < gH - RealVal(0.1)))}

        prop = {(proMF1): m == RealVal(1), proMF2: m == RealVal(2)}

        super().__init__(mode, vars, init, flow, inv, jump, prop, 0.001, goal)


if __name__ == '__main__':
    model = Watertank()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()
    '''
    const = model.reach(1)
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
    '''









