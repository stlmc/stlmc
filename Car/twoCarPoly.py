import os, sys, io
from .tcPoly import testcaseSTL
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
ZERO = RealVal(0)

def sin(degree):
    return degree - degree * degree * degree / RealVal(6)

def cos(degree):
    return degree - degree * degree / RealVal(2)

def tan(degree):
    return degree + degree * degree * degree


class CarPoly(Model):
    def __init__(self):
        mf = Bool('mf')
        ms = Bool('ms')
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
        constv1 = Real('constv1')
        constv2 = Real('constv2')
        constphi1 = Real('constphi1')
        consttheta1 = Real('consttheta1')
        constphi2 = Real('constphi2')
        consttheta2 = Real('consttheta2')

        mfNext = NextVar(mf)
        msNext = NextVar(ms)
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
        constv1Next = NextVar(constv1)
        constv2Next = NextVar(constv2)
        constphi1Next = NextVar(constphi1)
        consttheta1Next = NextVar(consttheta1)
        constphi2Next = NextVar(constphi2)
        consttheta2Next = NextVar(consttheta2)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proPZ = Bool('pz')
        proQZ = Bool('qz')

        mode = {}
        vars = {v1: (0, 10), v2: (0, 10), x1: (0, 100), x2: (0, 100), y1: (0, 100), y2: (0, 100), phi1: (-1, 1), phi2: (-1, 1), theta1: (-1.5, 1.5), theta2: (-1.5, 1.5)}
        init = And(And(mf == BoolVal(False), ms == BoolVal(False)), x1 > RealVal(0), x1 < RealVal(3), x2 > RealVal(5), x2 < RealVal(10), y1 < RealVal(10), y1 > RealVal(3), y2 > RealVal(3), y2 < RealVal(10), v1 >= RealVal(1), v1 <= RealVal(3), v2 >= RealVal(3), v2 <= RealVal(4), theta1 > RealVal(0), theta1 < RealVal(1), theta2 < RealVal(0), theta2 > -RealVal(1), phi1 <= RealVal(1), phi1 >= RealVal(0), phi2 <= RealVal(0), phi2 >= -RealVal(1), And(constv1 == v1, constv2 == v2, constphi1 == phi1, constphi2 == phi2, consttheta1 == theta1, consttheta2 == theta2) ) 

        flowx1 = constv1 * cos(consttheta1)
        flowy1 = constv1 * sin(consttheta1)
        flowx2 = constv2 * cos(consttheta2)
        flowy2 = constv2 * sin(consttheta2)
        flowtheta1 = constv1 * tan(constphi1)
        flowtheta2 = constv2 * tan(constphi2)
        flowphi1 = RealVal(0)
        flowphi2 = -(constphi2 - constphi1)

        flow = {And(mf == BoolVal(False), ms == BoolVal(False)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: RealVal(0), v2: -(constv2 - constv1), constv1: ZERO, constv2: ZERO, constphi1: ZERO, constphi2: ZERO, consttheta1: ZERO, consttheta2: ZERO}, \
               And(mf == BoolVal(False), ms == BoolVal(True)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: RealVal(0), v2: RealVal(5), constv1: ZERO, constv2: ZERO, constphi1: ZERO, constphi2: ZERO, consttheta1: ZERO, consttheta2: ZERO}, \
               And(mf == BoolVal(True), ms == BoolVal(False)): {x1: flowx1, y1: flowy1, x2: flowx2, y2: flowy2, theta1: flowtheta1, theta2: flowtheta2, phi1: flowphi1, phi2: flowphi2, v1: RealVal(0), v2: -RealVal(5), constv1: ZERO, constv2: ZERO, constphi1: ZERO, constphi2: ZERO, consttheta1: ZERO, consttheta2: ZERO}}
  
        inv = {And(mf == BoolVal(False), ms == BoolVal(False)): BoolVal(True), \
               And(mf == BoolVal(False), ms == BoolVal(True)): BoolVal(True), \
               And(mf == BoolVal(True), ms == BoolVal(False)): BoolVal(True)}
        
        jump = {And((((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) >= RealVal(36)), (((x2 - x1) * (x2 - x1) - (y2 - y1) * (y2 - y1)) <= RealVal(81))): And(And(mfNext == BoolVal(False), msNext == BoolVal(False)), x1Next == x1, x2Next == x2, v1Next == v1, v2Next == v2, phi1Next == phi1, phi2Next == phi2, theta1Next == theta1, theta2Next == theta2, y1Next == y1, y2Next == y2, And(constv1 == v1, constv2 == v2, constphi1 == phi1, constphi2 == phi2, consttheta1 == theta1, consttheta2 == theta2)), \
             (((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) < RealVal(36)): And(And(mfNext == BoolVal(True), msNext == BoolVal(False)), x1Next == x1, x2Next == x2, v1Next == v1, v2Next == v2, phi1Next == phi1, phi2Next == phi2, theta1Next == theta1, theta2Next == theta2, y1Next == y1, y2Next == y2, And(constv1 == v1, constv2 == v2, constphi1 == phi1, constphi2 == phi2, consttheta1 == theta1, consttheta2 == theta2)), \
             (((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) > RealVal(81)): And(And(mfNext == BoolVal(False), msNext == BoolVal(True)), x1Next == x1, x2Next == x2, v1Next == v1, v2Next == v2, phi1Next == phi1, phi2Next == phi2, theta1Next == theta1, theta2Next == theta2, y1Next == y1, y2Next == y2, And(constv1 == v1, constv2 == v2, constphi1 == phi1, constphi2 == phi2, consttheta1 == theta1, consttheta2 == theta2))}

        prop = {proPF: ((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) >= RealVal(100), proQF: ((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) < RealVal(36), proQZ: And(mf == BoolVal(True), ms == BoolVal(False)), proPZ: And((x1 - x2) >= -RealVal(0.5), (x1 - x2) <= RealVal(0.5), (y1 - y2) >= -RealVal(0.5), (y1 - y2) <= RealVal(0.5))}

        goal = ((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)) < RealVal(36)

        super().__init__(mode, vars, init, flow, inv, jump, prop, 1, testcaseSTL, "PolyCarReport", goal)


if __name__ == '__main__':
    model = CarNon()
    stlObject = STLHandler(model)
    model.reach(1)
    for i in range(len(model.stl)):
        formula = parseFormula(model.stl[i])
        print(formula)
        for j in range(0,2):
            (a, b, c,d) = model.modelCheck(formula, j)
            z3model = [z3Obj(i) for i in a]
            z3partition = [z3Obj(i) for i in b]
            z3full = z3Obj(c)
            s = z3.Solver()
            const = z3model + z3partition + [z3full]
            s.add(const)
            #print(s.to_smt2())
            stime1 = time.process_time()
            checkresult = s.check()
            etime1 = time.process_time()
            print(str(j) + ":  " + str(checkresult) + " " + str(etime1 - stime1))










