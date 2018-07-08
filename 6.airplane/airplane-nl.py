import os, sys, io
from tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from model import *
from core.STLHandler import *

g = RealVal(9.8055)
pi = RealVal(3.14159)
m = RealVal(20500.0)
qbw = RealVal(13.97 * 30 * 300)
qw = RealVal(13.97 * 300)
vT = RealVal(111.64)
c1 = -RealVal(0.770)
c2 = RealVal(0.02755)
c3 = RealVal(0.000105)
c4 = RealVal(0.0000016)
c8 = -RealVal(0.7336)
c9 = RealVal(0.00001587)

ZERO = RealVal(0)

class Airplane(Model):
    def __init__(self):
        ma = Real('ma')
        beta = Real('beta')
        p = Real('p')
        r = Real('r')
        phi = Real('phi')
        psi = Real('psi')

        xAIL = Real('xAIL')
        xRDR = Real('xRDR')
        gAIL = Real('gAIL')
        gRDR = Real('gRDR')
        gDir = Real('gDir')
   
        tau = Real('tau')

        maNext = NextVar(ma)
        betaNext = NextVar(beta)
        pNext = NextVar(p)
        rNext = NextVar(r)
        phiNext = NextVar(phi)
        psiNext = NextVar(psi)

        xAILNext = NextVar(xAIL)
        xRDRNext = NextVar(xRDR)
        gAILNext = NextVar(gAIL)
        gRDRNext = NextVar(gRDR)
        gDirNext = NextVar(gDir)

        tauNext = NextVar(tau)
        proPF = Bool('pf')
        proQF = Bool('qf')

        mode = {ma: (1, 4)}
        valrange1 = (-1.5, 1.5)
        valrange = (-3.14159, 3.14159)
        vars = {tau: (0, 0.5), beta: valrange1, p: valrange1, r: valrange1, phi: valrange1, psi: valrange1, xAIL: valrange, xRDR: valrange, gAIL: valrange, gRDR: valrange, gDir: valrange}

        init = And(ma == RealVal(1), And(beta == ZERO, p == ZERO, r == ZERO, phi == ZERO, psi == ZERO), \
                  And(gDir > RealVal(0.5), gDir < RealVal(0.7)), 
                   xAIL == ZERO, xRDR == ZERO, gAIL == ZERO, gRDR == ZERO)

        betaflow = qw * (-RealVal(0.02 * 180) / pi * beta + RealVal(0.021) * xAIL / RealVal(20) + RealVal(0.086) * xRDR / RealVal(30)) / (m * vT) - r + (vT / g) * cos(beta) * sin(phi) 
        pflow = (c1 * r + c2 * p) * r * tan(phi) + qbw * (c3 * (-RealVal(0.0008 * 180) / pi * beta + RealVal(0.05 / 20) * xAIL + RealVal(0.013 / 30) * xRDR) + c4 * (RealVal(0.02 * 180) / pi * beta + -RealVal(0.01) * xAIL / RealVal(20) + -RealVal(0.04) * xRDR / RealVal(30))) 
        rflow = (c8 * p - c2 * r) * r * tan(phi) + qbw * (c4 * (-RealVal(0.0008 * 180) / pi * beta + RealVal(0.05 / 20) * xAIL + RealVal(0.013 / 30) * xRDR) + c9 * (RealVal(0.02 * 180) / pi * beta + -RealVal(0.01 / 20) * xAIL + -RealVal(0.04 / 30) * xRDR)) 
        psiflow = (g / vT) * phi

        flow = {ma == RealVal(1): {beta: betaflow, p: pflow, r: rflow, phi: p, psi: psiflow, xAIL: RealVal(0.25), xRDR: RealVal(0.5), gAIL: ZERO, gRDR: ZERO, gDir: ZERO, tau: RealVal(1)}, \
               ma == RealVal(2): {beta: betaflow, p: pflow, r: rflow, phi: p, psi: psiflow, xAIL: RealVal(0.25), xRDR: -RealVal(0.5), gAIL: ZERO, gRDR: ZERO, gDir: ZERO, tau: RealVal(1)}, \
               ma == RealVal(3): {beta: betaflow, p: pflow, r: rflow, phi: p, psi: psiflow, xAIL: -RealVal(0.25), xRDR: RealVal(0.5), gAIL: ZERO, gRDR: ZERO, gDir: ZERO, tau: RealVal(1)}, \
               ma == RealVal(4): {beta: betaflow, p: pflow, r: rflow, phi: p, psi: psiflow, xAIL: -RealVal(0.25), xRDR: -RealVal(0.5), gAIL: ZERO, gRDR: ZERO, gDir: ZERO, tau: RealVal(1)}}


        inv = {ma == RealVal(1): And(tau >= RealVal(0), tau <= RealVal(0.5)), \
              ma == RealVal(2): And(tau >= RealVal(0), tau <= RealVal(0.5)), \
              ma == RealVal(3): And(tau >= RealVal(0), tau <= RealVal(0.5)), \
              ma == RealVal(4): And(tau >= RealVal(0), tau <= RealVal(0.5))} 

        newgAIL = (gDir - psi * RealVal(180 / 3.14)) * RealVal(0.5)
        newgRDR = beta * RealVal(0.35)

        jump = {And(tau == RealVal(0.5), gRDR >= xRDR, gAIL >= xAIL):  And(maNext == RealVal(1), And(betaNext == beta, pNext == p, rNext == r, phiNext == phi, psiNext == psi), xAILNext == xAIL, xRDRNext == xRDR, gAILNext == newgAIL, gRDRNext == newgRDR, gDirNext == gDir, tauNext == ZERO), \
               And(tau == RealVal(0.5), gRDR < xRDR, gAIL >= xAIL):  And(maNext == RealVal(2), And(betaNext == beta, pNext == p, rNext == r, phiNext == phi, psiNext == psi), xAILNext == xAIL, xRDRNext == xRDR, gAILNext == newgAIL, gRDRNext == newgRDR, gDirNext == gDir, tauNext == ZERO), \
               And(tau == RealVal(0.5), gRDR >= xRDR, gAIL < xAIL):  And(maNext == RealVal(3), And(betaNext == beta, pNext == p, rNext == r, phiNext == phi, psiNext == psi), xAILNext == xAIL, xRDRNext == xRDR, gAILNext == newgAIL, gRDRNext == newgRDR, gDirNext == gDir, tauNext == ZERO), \
               And(tau == RealVal(0.5), gRDR < xRDR, gAIL < xAIL):  And(maNext == RealVal(4), And(betaNext == beta, pNext == p, rNext == r, phiNext == phi, psiNext == psi), xAILNext == xAIL, xRDRNext == xRDR, gAILNext == newgAIL, gRDRNext == newgRDR, gDirNext == gDir, tauNext == ZERO)}

        goal = {ma == RealVal(1): Or(beta > RealVal(0.2), beta < -RealVal(0.2)), \
              ma == RealVal(2): Or(beta > RealVal(0.2), beta < -RealVal(0.2)), \
              ma == RealVal(3): Or(beta > RealVal(0.2), beta < -RealVal(0.2)), \
              ma == RealVal(4): Or(beta > RealVal(0.2), beta < -RealVal(0.2))}

        prop = {proPF: ma == RealVal(2), proQF: ma == RealVal(3)}
 
        super().__init__(mode, vars, init, flow, inv, jump, prop, goal)


if __name__ == '__main__':
    model = Airplane()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()












