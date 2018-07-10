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

V = -RealVal(3)


class Railroad(Model):
    def __init__(self):
        m = Real('mode')
        tx = Real('tx')   #train position
        bx = Real('bx')   #angualr 90: open, 0: close
        
        mNext = NextVar(m)
        txNext = NextVar(tx)
        bxNext = NextVar(bx)

        proPF = Bool('pf')
        proQF = Bool('qf')
        proQS = Bool('qs')
        mode = {m: (1,8)}
        vars = {tx: (-20, 100), bx: (0, 90)}
        init = And(m == RealVal(1), bx >= RealVal(0), bx < RealVal(1), tx >= RealVal(60), tx <= RealVal(70))

        flow = {m == RealVal(1): {tx: V, bx: RealVal(0)}, \
                m == RealVal(2): {tx: V, bx: RealVal(5)}, \
                m == RealVal(3): {tx: V, bx: RealVal(10)}, \
                m == RealVal(4): {tx: V, bx: -RealVal(10)}, \
                m == RealVal(5): {tx: V, bx: RealVal(0)}, \
                m == RealVal(6): {tx: V, bx: RealVal(0)}


        inv = {m == RealVal(1): And(tx >= RealVal(40), tx <= RealVal(95), bx >= RealVal(0), bx < RealVal(90)), \
               m == RealVal(2): And(tx < RealVal(40), tx >= RealVal(20), bx > RealVal(0), bx <= RealVal(90)), \
               m == RealVal(3): And(tx < RealVal(20), tx >= RealVal(5), bx > RealVal(0), bx <= RealVal(90)), \
               m == RealVal(4): And(tx < RealVal(0), tx >= -RealVal(30), bx >= RealVal(0), bx < RealVal(90)), \
               m == RealVal(5): And(bx < RealVal(5)), \
               m == RealVal(6): bxNext == bx}


        jump = {And(m == RealVal(1), tx < RealVal(40)): And(mNext == RealVal(2), bxNext == bx, txNext == tx), \
                And(m == RealVal(2), tx < RealVal(20)): And(mNext == RealVal(3), bxNext == bx, txNext == tx), \
                And(m == RealVal(3), tx < RealVal(5)): And(mNext == RealVal(4), bxNext == bx, txNext == tx), \
                And(m == RealVal(3), bx > RealVal(85)): And(mNext == RealVal(6), bxNext == bx, txNext == tx), \
                And(m == RealVal(6), tx < RealVal(5)): And(mNext == RealVal(4), bxNext == bx, txNext == tx), \
                And(m == RealVal(4), bx < RealVal(1)):  And(mNext == RealVal(5), bxNext == bx, txNext == tx), \
                m == RealVal(5): And(mNext == RealVal(1), bxNext == bx, txNext == (RealVal(85) + tx))} 

        prop = {proPF : m == RealVal(6), proQF: txNext >= tx, proQS: m == RealVal(1)}

        super().__init__(mode, vars, init, flow, inv, jump, prop, 1)


if __name__ == '__main__':
    model = Railroad()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()


