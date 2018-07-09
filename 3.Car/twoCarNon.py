import os, sys, io
from tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
import math 
from core.STLHandler import *

L1 = RealVal(1)
L2 = RealVal(1.5)
C = RealVal(2)
gT = RealVal(15)

class CarNon(Model):
    def __init__(self):
        m = Real('mode')
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

        mNext = NextVar(m)
        x1Next = NextVar(x1)
        x2Next = NextVar(x2)
        y1Next = NextVar(y1)
        y2Next = NextVar(y2)
        v1Next = NextVar(v1)
        v2Next = NextVar(v2)
        phi1Next = NextVar(phi1)
        theta1Next = NextVar(theta1)
        phi2Next = NextVar(phi2)
        theta2Next = NextVar(theta2)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proPZ = Bool('pz')
        proQZ = Bool('qz')

        X = cos(RealVal(20))

        mode = {m: (1, 3)}
        vars = {v1: (0, 10), v2: (0, 10), x1: (0, 100), x2: (0, 100), y1: (0, 100), y2: (0, 100), phi1: (-1, 1), phi2: (-1, 1), theta1: (-1.5, 1.5), theta2: (-1.5, 1.5)}
        init = And(m == RealVal(1), x1 > RealVal(0), x1 < RealVal(3), x2 > RealVal(5), x2 < RealVal(10), y1 < RealVal(10), y1 > RealVal(3), y2 > RealVal(3), y2 < RealVal(10), v1 >= RealVal(1), v1 <= RealVal(3), v2 >= RealVal(3), v2 <= RealVal(4), theta1 > RealVal(0), theta1 < RealVal(1), theta2 < RealVal(0), theta2 > -RealVal(1), phi1 <= RealVal(1), phi1 >= RealVal(0), phi2 <= RealVal(0), phi2 >= -RealVal(1)) 

        flowx1 = v1 * cos(theta1)
        flowy1 = v1 * sin(theta1)
        flowx2 = v2 * cos(theta2)
        flowy2 = v2 * sin(theta2)
        flowtheta1 = v1 * tan(phi1)
        flowtheta2 = v2 * tan(phi2)
        flowphi1 = RealVal(0)
        flowphi2 = -(phi2 - phi1)

        flow = {m == RealVal(1): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: RealVal(0), v2: -(v2 - v1)}, \
               m == RealVal(2): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: RealVal(0), v2: RealVal(5)}, \
               m == RealVal(3): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: RealVal(0), v2: -RealVal(5)}} 
        inv = {}
        
        jump = {And((((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) >= RealVal(36)), (((x2 - x1) * (x2 - x1) - (y2 - y1) * (y2 - y1)) <= RealVal(81))): And(mNext == RealVal(1), x1Next == x1, x2Next == x2, v1Next == v1, v2Next == v2, phi1Next == phi1, phi2Next == phi2, theta1Next == theta1, theta2Next == theta2, y1Next == y1, y2Next == y2), \
             (((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) < RealVal(36)): And(mNext == RealVal(3), x1Next == x1, x2Next == x2, v1Next == v1, v2Next == v2, phi1Next == phi1, phi2Next == phi2, theta1Next == theta1, theta2Next == theta2, y1Next == y1, y2Next == y2), \
             (((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) > RealVal(81)): And(mNext == RealVal(2), x1Next == x1, x2Next == x2, v1Next == v1, v2Next == v2, phi1Next == phi1, phi2Next == phi2, theta1Next == theta1, theta2Next == theta2, y1Next == y1, y2Next == y2)}

        prop = {proPF: m == RealVal(2), proQF: ((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) < RealVal(36), proQZ: m == RealVal(3), proPZ: And(x1 == x2, y1 == y2)}

        goal = {m == RealVal(3): And(Or(fx > gT + RealVal(1), fx < gT - RealVal(1)), Or(sx > gT + RealVal(1), sx < gT - RealVal(1))), \
               m == RealVal(2): And(Or(fx > gT + RealVal(1), fx < gT - RealVal(1)), Or(sx > gT + RealVal(1), sx < gT - RealVal(1))), \
               m == RealVal(1): And(Or(fx > gT + RealVal(1), fx < gT - RealVal(1)), Or(sx > gT + RealVal(1), sx < gT - RealVal(1)))}

        super().__init__(mode, vars, init, flow, inv, jump, prop, 0.5, goal)


if __name__ == '__main__':
    model = CarNon()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()











