import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from model import *

c1 = RealVal(0.41328)
c2 = -RealVal(0.366)
c3 = RealVal(0.08979)
c4 = -RealVal(0.0337)
c5 = RealVal(0.0001)
c6 = RealVal(2.821)
c7 = -RealVal(0.05231)
c8 = RealVal(0.10299)
c9 = -RealVal(0.00063)
c10 = RealVal(1.0)
c11 = RealVal(14.7)
c11P = RealVal(12.5)
c12 = RealVal(0.9)
c13 = RealVal(0.04)
c14 = RealVal(0.14)
c15 = RealVal(13.893)
c16 = -RealVal(35.2518)
c17 = RealVal(20.7364)
c18 = RealVal(2.6287)
c19 = -RealVal(1.592)
c20 = -RealVal(2.3421)
c21 = RealVal(2.7799)
c22 = -RealVal(0.3273)
c23 = RealVal(1.0)
c24 = RealVal(1.0)
c25 = RealVal(1.0)
c26 = RealVal(4.0)

tauI = RealVal(10)
h = RealVal(1)

ZERO = RealVal(0)

def mCf(w, x):
    return (c2 + c3 * w * x + c4 * w * x * x + c5 * w * w * x)

class Powertrain(Model):
    def __init__(self):
        mt = Real('mt')
        theta = Real('theta')
        p = Real('p')
        lambdas = Real('lambdas')

        pe = Real('pe')
        i = Real('i')
        tau = Real('tau')

        thetaI = Real('thetaI')
        w = Real('w')

        mtNext = NextVar(mt)
        thetaNext = NextVar(theta)
        pNext = NextVar(p)
        lambdasNext = NextVar(lambdas)

        peNext = NextVar(pe)
        iNext = NextVar(i)
        tauNext = NextVar(tau)

        thetaINext = NextVar(thetaI)
        wNext = NextVar(w)

        fcO =       (mCf(w,pe) / c11)
        fcP =      (mCf(w,pe) / c11P)
        fcC =     ((RealVal(10) + i + c13 * (c24 * lambdas - c11)) * mCf(w, pe) / c11)

        thetaHat = (c6 + c7 * theta + c8 * theta * theta + c9 * theta * theta * theta)
        dmAf = (RealVal(2) * thetaHat * (c20 * p * p + c21 * p + c22))
        dmC = (c12 * mCf(w,p))

        fc0 = (mCf(w,pe) / c11)
        fcP = (mCf(w,pe) / c11P)
        fcC = ((RealVal(1) + i + c13 * (c24 * lambdas - c11)) * mCf(w,pe) / c11) 

        mode = [mt]
        vars = {theta: (0, 180), p: (0, 10), lambdas: (0, 100), pe: (0, 10), i: (0, 100), tau: (0, 100), \
               thetaI: (0, 180), w: (0, 150)}

        init = And(theta == RealVal(8.8), p == RealVal(0.9833), lambdas  == RealVal(14.7), pe == RealVal(0.9), i == RealVal(0), tau == RealVal(0), w == RealVal(95),  thetaI == RealVal(70), mt == RealVal(1))

        thetaflow = RealVal(10) * (thetaI - theta)
        pflow = c1 * (dmAf - dmC)
        lambdasflow12 = c26 * (c15 + c16 * c25 * fcC + c17 * c25 * c25 * fcC * fcC + c18 * dmC + c19 * dmC * c25 * fcC - lambdas)
        peflow = c1 * (c23 * dmAf - mCf(w,pe))
        iflow = c14 * (c24 * lambdas - c11)

        lambdasflow3 = c26 * (c15 + c16 * c25 * fcP + c17 * c25 * c25 * fcP * fcP + c18 * dmC + c19 * dmC * c25 * fcP - lambdas)

        lambdasflow4 = c26 * (c15 + c16 * c25 * fcO + c17 * c25 * c25 * fcO * fcO + c18 * dmC + c19 * dmC * c25 * fcO - lambdas)
       
        flow = {mt == RealVal(1): {theta: thetaflow, p: pflow, lambdas: lambdasflow12, pe: peflow, i: iflow, tau: RealVal(1), thetaI: ZERO, w: ZERO}, \
               mt == RealVal(2): {theta: thetaflow, p: pflow, lambdas: lambdasflow12, pe: peflow, i: iflow, tau: RealVal(1), thetaI: ZERO, w: ZERO}, \
               mt == RealVal(3): {theta: thetaflow, p: pflow, lambdas: lambdasflow3, pe: ZERO, i: ZERO, tau: RealVal(1), thetaI: ZERO, w: ZERO}, \
               mt == RealVal(4): {theta: thetaflow, p: pflow, lambdas: lambdasflow4, pe: ZERO, i: ZERO, tau: RealVal(1), thetaI: ZERO, w: ZERO}}

        inv = {mt == RealVal(1): tau <= tauI, \
              mt == RealVal(2): theta <= RealVal(70), \
              mt == RealVal(3): theta >= RealVal(50), \
              mt == RealVal(4): BoolVal(True)}

        jump = {And(mt == RealVal(1), tau == tauI): And(mtNext == RealVal(2), thetaNext == theta, pNext == p, lambdasNext == lambdas, And(thetaINext == thetaI, wNext == w, peNext == pe, iNext == i, tauNext == tau)), \
               And(mt == RealVal(2), theta == RealVal(70)): And(mtNext == RealVal(3), thetaNext == theta, pNext == p, lambdasNext == lambdas, And(thetaINext == thetaI, wNext == w, peNext == pe, iNext == i, tauNext == tau)), \
               mt == RealVal(2): And(Or(mtNext == RealVal(2), mtNext == RealVal(4)), thetaNext == theta, pNext == p, lambdasNext == lambdas, And(thetaINext == thetaI, wNext == w, peNext == pe, iNext == i, tauNext == tau)), \
               And(mt == RealVal(3), theta == RealVal(50)): And(mtNext == RealVal(2), thetaNext == theta, pNext == p, lambdasNext == lambdas, And(thetaINext == thetaI, wNext == w, peNext == pe, iNext == i, tauNext == tau))}

        prop = {}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Powertrain()
    const = model.reach(2)

    output = io.StringIO()
    printObject = dRealHandler(const, output, model.variables, model.flowDict)
    printObject.callAll()
    dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
    dRealname = dRealname[:-3]
    dRealname += '.smt2'
    f = open(dRealname, 'w')
    f.write(output.getvalue())
    f.close()





