import os, sys, io
from tcLinear import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
from core.STLHandler import *

L1 = RealVal(1)
L2 = RealVal(1.5)
V1Acc = RealVal(4.0)
V1Dec = RealVal(0.3)
V2Acc = RealVal(3.0)
V2Dec = RealVal(0.5)
Keep = RealVal(1)
#Acc: 1, Keep: 0, Dec: -1

class Car(Model):
    def __init__(self):
        mx1 = Real('mx1')
        mx2 = Real('mx2')
        x1 = Real('x1')
        x2 = Real('x2')
        mx1Next = NextVar(mx1)
        mx2Next = NextVar(mx2)
        x1Next = NextVar(x1)
        x2Next = NextVar(x2)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proQZ = Bool('qz')

        mode = {mx1: (-1, 1), mx2: (-1, 1)}
        vars = {x1: (0, 100), x2: (0, 100)}
        init = And(And(mx1 == RealVal(1), mx2 == RealVal(1)), x1 == RealVal(0), x2 == RealVal(3))


        flow = {And(mx1 == RealVal(1), mx2 == RealVal(1)): {x1: V1Acc, x2: V2Acc}, \
               And(mx1 == RealVal(1), mx2 == RealVal(0)): {x1: V1Acc, x2: Keep}, \
               And(mx1 == RealVal(1), mx2 == -RealVal(1)): {x1: V1Acc, x2: V2Dec}, \
               And(mx1 == RealVal(0), mx2 == RealVal(1)): {x1: Keep, x2: V2Acc}, \
               And(mx1 == RealVal(0), mx2 == RealVal(0)): {x1: Keep, x2: Keep}, \
               And(mx1 == RealVal(0), mx2 == -RealVal(1)): {x1: Keep, x2: V2Dec}, \
               And(mx1 == -RealVal(1), mx2 == RealVal(1)): {x1: V1Dec, x2: V2Acc}, \
               And(mx1 == -RealVal(1), mx2 == RealVal(0)): {x1: V1Dec, x2: Keep}, \
               And(mx1 == -RealVal(1), mx2 == -RealVal(1)): {x1: V1Dec, x2: V2Dec}}
  
        inv = {And(mx1 == RealVal(1), mx2 == RealVal(1)): x2 >= x1, \
               And(mx1 == RealVal(1), mx2 == RealVal(0)): x2 >= x1, \
               And(mx1 == RealVal(1), mx2 == -RealVal(1)): x2 >= x1, \
               And(mx1 == RealVal(0), mx2 == RealVal(1)): x2 >= x1, \
               And(mx1 == RealVal(0), mx2 == RealVal(0)): x2 >= x1, \
               And(mx1 == RealVal(0), mx2 == -RealVal(1)): x2 >= x1, \
               And(mx1 == -RealVal(1), mx2 == RealVal(1)): x2 >= x1, \
               And(mx1 == -RealVal(1), mx2 == RealVal(0)): x2 >= x1, \
               And(mx1 == -RealVal(1), mx2 == -RealVal(1)): x2 >= x1}


        jump = {x2 - x1 <  RealVal(1): And(And(mx1Next == -RealVal(1), mx2Next == RealVal(1)), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(1), (x2 - x1) < RealVal(2)): And(And(mx1Next == RealVal(0), mx2Next == RealVal(1)), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(2), (x2 - x1) < RealVal(3)): And(And(mx1Next == RealVal(1), mx2Next == RealVal(1)), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(3), (x2 - x1) < RealVal(4)): And(And(mx1Next == RealVal(1), mx2Next == RealVal(0)), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(4), (x2 - x1) < RealVal(5)): And(And(mx1Next == RealVal(0), mx2Next == -RealVal(1)), x1Next == x1, x2Next == x2), \
               x2 - x1 >= RealVal(5): And(And(mx1Next == RealVal(1)), mx2Next == -RealVal(1), x1Next == x1, x2Next == x2)}

        prop = {proPF : mx1 == -RealVal(1), proQF: x2 - x1 < RealVal(1), proQZ: x2 > x1, }

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Car()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()











