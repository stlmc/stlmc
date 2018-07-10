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
        m = Real('mode')
        x1 = Real('x1')
        x2 = Real('x2')
        mNext = NextVar(m)
        x1Next = NextVar(x1)
        x2Next = NextVar(x2)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proQZ = Bool('qz')

        mode = {m: (1, 9)}
        vars = {x1: (0, 100), x2: (0, 100)}
        init = And(m == RealVal(1), x1 >= RealVal(0), x1 <= RealVal(1), x2 <= RealVal(10), x2 >= RealVal(3))


        flow = {m == RealVal(1): {x1: V1Acc, x2: V2Acc}, \
               m == RealVal(2): {x1: V1Acc, x2: Keep}, \
               m == RealVal(3): {x1: Keep, x2: V2Acc}, \
               m == RealVal(4): {x1: Keep, x2: V2Dec}, \
               m == RealVal(5): {x1: V1Dec, x2: V2Acc}, \
               m == RealVal(6): {x1: V1Dec, x2: V2Dec}}
  
        inv = {m == RealVal(1): x2 >= x1, \
               m == RealVal(2): x2 >= x1, \
               m == RealVal(3): x2 >= x1, \
               m == RealVal(4): x2 >= x1, \
               m == RealVal(5): x2 >= x1, \
               m == RealVal(6): x2 >= x1}


        jump = {And((x2 - x1) >= RealVal(2), (x2 - x1) < RealVal(3)): And(mNext == RealVal(1), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(3), (x2 - x1) < RealVal(4)): And(mNext == RealVal(2), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(1), (x2 - x1) < RealVal(2)): And(mNext == RealVal(3), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(4), (x2 - x1) < RealVal(5)): And(mNext == RealVal(4), x1Next == x1, x2Next == x2), \
               x2 - x1 <  RealVal(1): And(mNext == RealVal(5), x1Next == x1, x2Next == x2), \
               x2 - x1 >= RealVal(5): And(mNext == RealVal(6), x1Next == x1, x2Next == x2)}

        prop = {proPF : m == RealVal(6), proQF: x2 - x1 < RealVal(1), proQZ: x2 > x1 }

        super().__init__(mode, vars, init, flow, inv, jump, prop, 1)


if __name__ == '__main__':
    model = Car()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()











