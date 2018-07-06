import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
import math 

L1 = RealVal(1)
L2 = RealVal(1.5)
C = RealVal(2)

#Acc: 1, Keep: 0, Dec: -1
class CarNon(Model):
    def __init__(self):
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

        mode = [mx1, mx2] 
        vars = {v1: (-15, 15), v2: (-15, 15), x1: (-50, 50), x2: (-50, 50), y1: (-50, 50), y2: (-50, 50), phi1: (-15, 15), phi2: (-15, 15), theta1: (-5, 5), theta2: (-5, 5)}
        init = And(And(mx1 == RealVal(1), mx2 == RealVal(1)), x1 == RealVal(0), x2 == RealVal(10), y1 == RealVal(10), y2 == RealVal(10), v1 == RealVal(3), v2 == RealVal(4), theta1 == RealVal(0), theta2 == RealVal(0), phi1 == RealVal(5), phi2 == -RealVal(5)) 

        flowx1 = v1 * cos(theta1)
        flowy1 = v1 * sin(theta1)
        flowx2 = v2 * cos(theta2)
        flowy2 = v2 * sin(theta2)
        flowtheta1 = v1 / L1 * tan(phi1)
        flowtheta2 = v2 / L2 * tan(phi2)
        flowphi1 = -phi1
        flowphi2 = -(phi2 - phi1)
        v1keep = -v1
        v2keep = -(v2 - v1)
        v1acc = C
        v2acc = C
        v1dec = -C
        v2dec = -C
 

        flow = {And(mx1 == RealVal(1), mx2 == RealVal(1)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1acc, v2: v2acc}, \
               And(mx1 == RealVal(1), mx2 == RealVal(0)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1acc, v2: v2keep}, \
               And(mx1 == RealVal(1), mx2 == -RealVal(1)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1acc, v2: v2dec}, \
               And(mx1 == RealVal(0), mx2 == RealVal(1)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1keep, v2: v2acc}, \
               And(mx1 == RealVal(0), mx2 == RealVal(0)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1keep, v2: v2keep}, \
               And(mx1 == RealVal(0), mx2 == -RealVal(1)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1keep, v2: v2dec}, \
               And(mx1 == -RealVal(1), mx2 == RealVal(1)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1dec, v2: v2acc}, \
               And(mx1 == -RealVal(1), mx2 == RealVal(0)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1dec, v2: v2keep}, \
               And(mx1 == -RealVal(1), mx2 == -RealVal(1)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: v1dec, v2: v2dec}}
 
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
        for c in const:
            s.add(z3Obj(c))
#        print(s.to_smt2())
        print(s.check())
    except z3constODEerror:
        print("receive nonlinear ODE")












