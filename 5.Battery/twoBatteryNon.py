import os, sys, io
from tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
import math 
from core.STLHandler import *

K = RealVal(0.122)
C = RealVal(0.166)

#On: 1, Off: 0, Dead: -1

class Battery(Model):
    def __init__(self):
        m = Real('mode')
        d1 = Real('d1')
        d2 = Real('d2')
        g1 = Real('g1')
        g2 = Real('g2')
        mNext = NextVar(m)
        d1Next = NextVar(d1)
        d2Next = NextVar(d2)
        g1Next = NextVar(g1)
        g2Next = NextVar(g2)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proPZ = Bool('pz')
        proQZ = Bool('qz')
        proMT = Bool('mo')
        proMO = Bool('mt')

        mode = {m: (1,5)}
        vars = {d1: (-10, 10), d2: (-10, 10), g1: (-10, 10), g2: (-10, 10)}
        init = And(m == RealVal(1), g1 == RealVal(8.5), d1 == RealVal(0), g2 == RealVal(7.5), d2 == RealVal(0))

        flow = {m == RealVal(1): {d1: (RealVal(0.5) / C) - (K * d1), d2: (RealVal(0.5) / C) - (K * d2), g1: -RealVal(0.5), g2: -RealVal(0.5)}, \
               m == RealVal(2): {d1: (RealVal(1) / C) - (K * d1), d2: -(K * d2), g1: -RealVal(1), g2: RealVal(0)}, \
               m == RealVal(3): {d1: -(K * d1), d2: (RealVal(1) / C) - (K * d2), g1: RealVal(0), g2: -RealVal(1)}, \
               m == RealVal(4): {d1: RealVal(0), d2: (RealVal(1) / C) - (K * d2), g1: RealVal(0), g2: -RealVal(1)}, \
               m == RealVal(5): {d1: (RealVal(1) / C) - (K * d1), d2: RealVal(0), g1: -RealVal(1), g2: RealVal(0)}, \
               m == RealVal(6): {d1: RealVal(0), d2: RealVal(0), g1: RealVal(0), g2: RealVal(0)}}
  
        inv = {}

        jump = {And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(mNext == RealVal(1), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2), \
               And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(mNext == RealVal(2), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2), \
               And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(mNext == RealVal(3), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2), \
               And(g1 <= (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(mNext == RealVal(4), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2), \
               And(g1 > (RealVal(1) - C) * d1, g2 <= (RealVal(1) - C) * d2): And(mNext == RealVal(5), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2), \
               And(g1 <= (RealVal(1) - C) * d1, g2 <= (RealVal(1) - C) * d2): And(mNext == RealVal(6), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2)}

        prop = {proPF: m == RealVal(6), proQF: m == RealVal(4), proQZ: m == RealVal(3), proMT: m == RealVal(2), proMO: m == RealVal(1), proPZ: m == RealVal(5)}


        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Battery()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()











