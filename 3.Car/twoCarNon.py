import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.interface import *
from core.dRealHandler import *
from model import *
import math 

L1 = RealVal(1)
L2 = RealVal(1.5)
C = RealVal(2)

#Acc: 1, Keep: 0, Dec: -1
class CarNon(Model):
    mx1 = Real('mx1')
    mx2 = Real('mx2')
    x1 = Real('x1')
    x2 = Real('x2')
    y1 = Real('y1')
    y2 = Real('y2')
    v1 = Real('v1')
    v2 = Real('v2')
    phi1 = Real('phi1')
    theta1 = Real('theta1')
    phi2 = Real('phi2')
    theta2 = Real('theta2')
    mx1Next = NextVar(mx1)
    mx2Next = NextVar(mx2)
    y1Next = NextVar(x1)
    y2Next = NextVar(x2)
    y1Next = NextVar(y1)
    y2Next = NextVar(y2)
    phi1Next = NextVar(phi1)
    theta1Next = NextVar(theta1)
    phi2Next = NextVar(phi2)
    theta2Next = NextVar(theta2)
    proPF = Bool('pf')
    proQF = Bool('qf')
    X = cos(RealVal(20))
    def __init__(self):
        mode = [self.mx1, self.mx2] 
        vars = {self.v1: (-15, 15), self.v2: (-15, 15), self.x1: (-50, 50), self.x2: (-50, 50), self.y1: (-50, 50), self.y2: (-50, 50), self.phi1: (-15, 15), self.phi2: (-15, 15), self.theta1: (-5, 5), self.theta2: (-5, 5)}
        init = And(And(self.mx1 == RealVal(1), self.mx2 == RealVal(1)), self.x1 == RealVal(0), self.x2 == RealVal(10), self.y1 == RealVal(10), self.y2 == RealVal(10), self.v1 == RealVal(3), self.v2 == RealVal(4), self.theta1 == RealVal(0), self.theta2 == RealVal(0), self.phi1 == RealVal(5), self.phi2 == -RealVal(5)) 

        flowx1 = self.v1 * cos(self.theta1)
        flowy1 = self.v1 * sin(self.theta1)
        flowx2 = self.v2 * cos(self.theta2)
        flowy2 = self.v2 * sin(self.theta2)
        flowtheta1 = self.v1 / L1 * tan(self.phi1)
        flowtheta2 = self.v2 / L2 * tan(self.phi2)
        flowphi1 = -self.phi1
        flowphi2 = -(self.phi2 - self.phi1)
        v1keep = -self.v1
        v2keep = -(self.v2 - self.v1)
        v1acc = C
        v2acc = C
        v1dec = -C
        v2dec = -C
 

        flow = {And(self.mx1 == RealVal(1), self.mx2 == RealVal(1)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1acc, self.v2: v2acc}, \
               And(self.mx1 == RealVal(1), self.mx2 == RealVal(0)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1acc, self.v2: v2keep}, \
               And(self.mx1 == RealVal(1), self.mx2 == -RealVal(1)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1acc, self.v2: v2dec}, \
               And(self.mx1 == RealVal(0), self.mx2 == RealVal(1)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1keep, self.v2: v2acc}, \
               And(self.mx1 == RealVal(0), self.mx2 == RealVal(0)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1keep, self.v2: v2keep}, \
               And(self.mx1 == RealVal(0), self.mx2 == -RealVal(1)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1keep, self.v2: v2dec}, \
               And(self.mx1 == -RealVal(1), self.mx2 == RealVal(1)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1dec, self.v2: v2acc}, \
               And(self.mx1 == -RealVal(1), self.mx2 == RealVal(0)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1dec, self.v2: v2keep}, \
               And(self.mx1 == -RealVal(1), self.mx2 == -RealVal(1)): {self.x1: flowx1, self.y1: flowy1, self.x2: flowx2, self.y2: flowy2, self.theta1: flowtheta1, self.theta2: flowtheta2, self.phi1: flowphi1, self.phi2: flowphi2, self.v1: v1dec, self.v2: v2dec}}
 
        inv = {}
        
        jump = {}

        prop = {}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = CarNon()
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












