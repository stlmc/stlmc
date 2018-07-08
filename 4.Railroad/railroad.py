import os, sys, io
from tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
from core.STLHandler import *

FAR = RealVal(1)
APPROACH = RealVal(2)
NEAR = RealVal(3)
PAST = RealVal(4)

OPEN = RealVal(1)
CLOSE = RealVal(2)

V = RealVal(3)

#Far: 1, approach: 2, Near: 3, Past: 4

class Railroad(Model):
    def __init__(self):
        tm = Real('tm')   #train mode
        bm = Real('bm')   #bar mode
        tx = Real('tx')   #train position
        bx = Real('bx')   #angualr 90: open, 0: close
        tmNext = NextVar(tm)
        txNext = NextVar(tx)
        bmNext = NextVar(bm)
        bxNext = NextVar(bx)
        proPF = Bool('pf')
        proQF = Bool('qf')
        mode = {tm: (1, 4), bm: (1,2)}
        vars = {tx: (-20, 100), bx: (0, 90)}
        init = And(tm == FAR, bm == CLOSE, bx == RealVal(0), tx >= RealVal(5), tx <= RealVal(8))

        flow = {And(tm == FAR, bm == CLOSE): {tx: V, bx: RealVal(0)}, \
                And(tm == FAR, bm == OPEN): {tx: V, bx: RealVal(0)}, \
                And(tm == APPROACH, bm == CLOSE): {tx: V, bx: -RealVal(5)}, \
                And(tm == APPROACH, bm == OPEN): {tx: V, bx: RealVal(5)}, \
                And(tm == NEAR, bm == CLOSE): {tx: V, bx: -RealVal(5)}, \
                And(tm == NEAR, bm == OPEN): {tx: V, bx: RealVal(5)}, \
                And(tm == PAST, bm == CLOSE): {tx: V, bx: -RealVal(5)}, \
                And(tm == PAST, bm == OPEN): {tx: V, bx: RealVal(5)}}


        inv = {And(tm == FAR, bm == CLOSE): And(tx >= RealVal(40), tx <= RealVal(95), bx >= RealVal(0), bx < RealVal(90)), \
                And(tm == FAR, bm == OPEN): And(tx >= RealVal(40), tx <= RealVal(95), bx > RealVal(0), bx <= RealVal(90)), \
                And(tm == APPROACH, bm == CLOSE):  And(tx < RealVal(40), tx >= RealVal(20), bx >= RealVal(0), bx < RealVal(90)), \
                And(tm == APPROACH, bm == OPEN): And(tx < RealVal(40), tx >= RealVal(20), bx > RealVal(0), bx <= RealVal(90)), \
                And(tm == NEAR, bm == CLOSE): And(tx < RealVal(20), tx >= RealVal(5), bx >= RealVal(0), bx < RealVal(90)), \
                And(tm == NEAR, bm == OPEN): And(tx < RealVal(20), tx >= RealVal(5), bx > RealVal(0), bx <= RealVal(90)), \
                And(tm == PAST, bm == CLOSE): And(tx < RealVal(5), tx >= -RealVal(10), bx >= RealVal(0), bx < RealVal(90)), \
                And(tm == PAST, bm == OPEN): And(tx < RealVal(5), tx >= -RealVal(10),
bx > RealVal(0), bx <= RealVal(90))}


        jump = {And(bm == CLOSE, tm == APPROACH): And(bmNext == OPEN, bxNext == bx, tmNext == tm, txNext == tx), \
                And(bm == OPEN, tm == PAST): And(bmNext == CLOSE, tmNext == tm, bxNext == bx), \
                And(tm == NEAR, tx < RealVal(5)): And(tmNext == PAST, bxNext == bx, txNext == tx, bmNext == bm), \
                And(tm == PAST, tx < -RealVal(5)): And(tmNext == FAR, bxNext == bx, txNext == RealVal(85), bmNext == bm), \
                And(tm == FAR, tx < RealVal(40)): And(tmNext == APPROACH, bxNext == bx, txNext == tx, bmNext == bm), \
                And(tm == APPROACH,tx < RealVal(2)): And(tmNext == NEAR, bxNext == bx, txNext == tx, bmNext == bm)} 

        prop = {}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Railroad()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()





