import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.interface import *
from core.dRealHandler import *
from model import *

g = RealVal(9.8055)
pi = RealVal(3.14159)
vT = RealVal(92.827)
yBTA = -RealVal(0.0995)
lBTA = -RealVal(1.7009)
lP = -RealVal(1.1846)
lR = RealVal(0.2239)
nBTA = RealVal(0.4074)
nP = -RealVal(0.05627)
nR = -RealVal(0.1880)
yRDR = RealVal(0.7403)
lAIL = RealVal(0.5313)
lRDR = RealVal(0.04976)
nAIL = RealVal(0.00568)
nRDR = -RealVal(0.10659)

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
        tauNext = NextVar(tau)
        proPF = Bool('pf')
        proQF = Bool('qf')

        mode = [ma]
        valrange = (-3.14159, 3.14159)
        vars = {tau: (0, 0.5), beta: valrange, p: valrange, r: valrange, phi: valrange, psi: valrange, xAIL: valrange, xRDR: valrange, gAIL: valrange, gRDR: valrange}

        init = And(And(beta == ZERO, p == ZERO, r == ZERO, phi == ZERO, psi == ZERO), \
                   xAIL == ZERO, xRDR == ZERO, gAIL == ZERO, gRDR == ZERO)

        betaflow = yBTA * beta - r + (g / vT) * phi + yRDR * xRDR
        pflow = lBTA * beta + lP * p + lR * r + lAIL * xAIL + lRDR * xRDR
        rflow = nBTA * beta + nP * p + nR * r + nAIL * xAIL + nRDR * xRDR
        psiflow = (g / vT) * phi

        flow = {ma == RealVal(1): {beta: betaflow, p: pflow, r: rflow, phi: p, psi: psiflow, xAIL: RealVal(0.25), xRDR: RealVal(0.5), gAIL: ZERO, gRDR: ZERO, tau: RealVal(1)}, \
               ma == RealVal(2): {beta: betaflow, p: pflow, r: rflow, phi: p, psi: psiflow, xAIL: RealVal(0.25), xRDR: -RealVal(0.5), gAIL: ZERO, gRDR: ZERO, tau: RealVal(1)}, \
               ma == RealVal(3): {beta: betaflow, p: pflow, r: rflow, phi: p, psi: psiflow, xAIL: -RealVal(0.25), xRDR: RealVal(0.5), gAIL: ZERO, gRDR: ZERO, tau: RealVal(1)}, \
               ma == RealVal(4): {beta: betaflow, p: pflow, r: rflow, phi: p, psi: psiflow, xAIL: -RealVal(0.25), xRDR: -RealVal(0.5), gAIL: ZERO, gRDR: ZERO, tau: RealVal(1)}}


        inv = {ma == RealVal(1): And(tau >= RealVal(0), tau <= RealVal(0.5)), \
              ma == RealVal(2): And(tau >= RealVal(0), tau <= RealVal(0.5)), \
              ma == RealVal(3): And(tau >= RealVal(0), tau <= RealVal(0.5)), \
              ma == RealVal(4): And(tau >= RealVal(0), tau <= RealVal(0.5))} 

        jump = {And(tau == RealVal(0.5), gRDR >= xRDR, gAIL >= xAIL):  And(And(betaNext == beta, pNext == p, rNext == r, phiNext == phi, psiNext == psi), xAILNext == xAIL, xRDRNext == xRDR, gAILNext == gAIL, gRDRNext == gRDR, tauNext == ZERO), \
               And(tau == RealVal(0.5), gRDR < xRDR, gAIL >= xAIL):  And(And(betaNext == beta, pNext == p, rNext == r, phiNext == phi, psiNext == psi), xAILNext == xAIL, xRDRNext == xRDR, gAILNext == gAIL, gRDRNext == gRDR, tauNext == ZERO), \
               And(tau == RealVal(0.5), gRDR >= xRDR, gAIL < xAIL):  And(And(betaNext == beta, pNext == p, rNext == r, phiNext == phi, psiNext == psi), xAILNext == xAIL, xRDRNext == xRDR, gAILNext == gAIL, gRDRNext == gRDR, tauNext == ZERO), \
               And(tau == RealVal(0.5), gRDR < xRDR, gAIL < xAIL):  And(And(betaNext == beta, pNext == p, rNext == r, phiNext == phi, psiNext == psi), xAILNext == xAIL, xRDRNext == xRDR, gAILNext == gAIL, gRDRNext == gRDR, tauNext == ZERO)}

        prop = {proPF: And(beta > RealVal(0.2), beta < RealVal(0.2))}
 
        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Airplane()
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












