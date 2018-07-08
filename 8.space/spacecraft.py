import os, sys, io
from tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from model import *
from core.STLHandler import *

n = RealVal(4.7351)
m = RealVal(500)
Fx = -RealVal(5)
Fy = -RealVal(5)
K1 = RealVal(1)
K2 = RealVal(2)
T1 = RealVal(10)
T2 = RealVal(80)

def distance(a, b):
    return Sqrt(a * a + b * b)

class Space(Model):
    def __init__(self):
        ms = Real('ms')
        
        x = Real('x')
        vx = Real('vx')
        ax = Real('ax')

        y = Real('y')
        vy = Real('vy')
        ay = Real('ay')

        tmr = Real('tmr')

        msNext =NextVar(ms)
        xNext = NextVar(x)
        vxNext = NextVar(vx)
        axNext = NextVar(ax)

        yNext = NextVar(y)
        vyNext = NextVar(vy)
        ayNext = NextVar(ay)

        tmrNext = NextVar(tmr)

        proPF = Bool('pf')
        proQF = Bool('qf')
        proQZ = Bool('qz')

        mode = {ms: (1, 3)}
        vars = {tmr: (0, 100), x: (0, 150), vx: (0, 150), ax: (0, 150), y: (0, 150), vy: (0, 150), ay: (0, 150)}

        init = And(tmr == RealVal(0), ms == RealVal(1), x >= RealVal(90), x <= RealVal(120), y >= RealVal(90), y <= RealVal(120), And(vx >= RealVal(10), vx <= RealVal(12), vy >= RealVal(10), vy <= RealVal(12)), And(ax >= RealVal(2), ax <= RealVal(4), ay >= RealVal(2), ay <= RealVal(4)))


        flowax1 = RealVal(3) * n * n * x + RealVal(2) * n * vy + K1 * Fx / m
        floway1 = -RealVal(2) * n * vx + K1 * Fy / m

        flowax2 = RealVal(3) * n * n * x + RealVal(2) * n * vy + K2 * Fx / m
        floway2 = -RealVal(2) * n * vx + K2 * Fy / m

        flowax3 = RealVal(3) * n * n * x + RealVal(2) * n * vy
        floway3 = -RealVal(2) * n * vx

        flow = {ms == RealVal(1): {tmr: RealVal(1), x: vx, vx: ax, ax: flowax1, y: vy, vy: ay, ay: floway1}, \
               ms == RealVal(2): {tmr: RealVal(1), x: vx, vx: ax, ax: flowax2, y: vy, vy: ay, ay: floway2}, \
               ms == RealVal(3): {tmr: RealVal(1), x: vx, vx: ax, ax: flowax3, y: vy, vy: ay, ay: floway3}}

        inv = {ms == RealVal(1): And(tmr <= T2, distance(x, y) >= RealVal(100)), \
               ms == RealVal(2): And(tmr <= T2, distance(x, y) <= RealVal(100)), \
               ms == RealVal(3): tmr >= T1} 

        jump = {And(ms == RealVal(1), distance(x, y) <= RealVal(100)): And(msNext == RealVal(2), xNext == x, vxNext == vx, axNext == ax, yNext == y, vyNext == vy, ayNext == ay, tmrNext == tmr), \
               And(ms == RealVal(2), distance(x, y) >= RealVal(100)): And(msNext == RealVal(1), xNext == x, vxNext == vx, axNext == ax, yNext == y, vyNext == vy, ayNext == ay, tmrNext == tmr), \
               And(ms == RealVal(1), tmr >= T1, tmr <= T2): And(Or(msNext == RealVal(3), msNext == RealVal(1)), xNext == x, vxNext == vx, axNext == ax, yNext == y, vyNext == vy, ayNext == ay, tmrNext == tmr), \
               And(ms == RealVal(2), tmr >= T1, tmr <= T2): And(Or(msNext == RealVal(3), msNext == RealVal(2)), xNext == x, vxNext == vx, axNext == ax, yNext == y, vyNext == vy, ayNext == ay, tmrNext == tmr) }
 

        prop = {proPF: ms == RealVal(3), proQF: ms == RealVal(2), proQZ: tmrNext >= tmr}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Space()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()










