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


#Far: 1, approach: 2, Near: 3, Past: 4

class Railroad(Model):
    def __init__(self):
        m = Real('mode')
        tx = Real('tx')   #train position
        bx = Real('bx')   #angualr 90: open, 0: close
        vbx = Real('vbx')
        
        mNext = NextVar(m)
        txNext = NextVar(tx)
        bxNext = NextVar(bx)
        vbxNext = NextVar(vbx)

        proPF = Bool('pf')
        proQF = Bool('qf')
        proQS = Bool('qs')
        mode = {m: (1,8)}
        vars = {vbx: (-20, 20), tx: (-20, 100), bx: (0, 90)}
        init = And(m == RealVal(1), vbx == RealVal(0), bx == RealVal(0), tx >= RealVal(60), tx <= RealVal(70))

        flow = {m == RealVal(1): {tx: V, bx: RealVal(0), vbx: RealVal(0)}, \
                m == RealVal(2): {tx: V, bx: RealVal(0), vbx: RealVal(0)}, \
                m == RealVal(3): {tx: V, bx: vbx, vbx: RealVal(5)}, \
                m == RealVal(4): {tx: V, bx: vbx, vbx: RealVal(10)}, \
                m == RealVal(5): {tx: V, bx: vbx, vbx: -RealVal(5)}, \
                m == RealVal(6): {tx: V, bx: RealVal(0), vbx: RealVal(0)}}


        inv = {m == RealVal(1): And(tx >= RealVal(40), tx <= RealVal(95), bx >= RealVal(0), bx < RealVal(90)), \
               m == RealVal(2):  And(tx < RealVal(40), tx >= RealVal(20), bx >= RealVal(0), bx < RealVal(90)), \
               m == RealVal(3): And(tx < RealVal(40), tx >= RealVal(20), bx > RealVal(0), bx <= RealVal(90)), \
               m == RealVal(4): And(tx < RealVal(20), tx >= RealVal(5), bx > RealVal(0), bx <= RealVal(90)), \
               m == RealVal(5): And(tx < RealVal(5), tx >= -RealVal(10), bx >= RealVal(0), bx < RealVal(90)), \
               m == RealVal(6): And(tx < RealVal(5), tx >= -RealVal(10), bx > RealVal(0), bx <= RealVal(90))}


        jump = {And(m == RealVal(1), tx < RealVal(40)): And(m == RealVal(2), bxNext == bx, txNext == tx, vbxNext == vbx), \
                And(m == RealVal(2),tx < RealVal(30)): And(m == RealVal(3), bxNext == bx, txNext == tx, vbxNext == vbx), \
                And(m == RealVal(3), tx < RealVal(20)): And(m == RealVal(4), vbxNext == vbx, bxNext == bx, txNext == tx), \
                And(m == RealVal(4), tx < RealVal(5)): And(m == RealVal(5), bxNext == bx, vbxNext == vbx, txNext == tx), \
                And(m == RealVal(5), tx < RealVal(0)):  And(m == RealVal(6), vbxNext == vbx, bxNext == bx, txNext == tx), \
                And(m == RealVal(6), tx < -RealVal(5)): And(m == RealVal(1), bxNext == bx, txNext == RealVal(85), vbxNext == vbx)} 

        prop = {proPF : m == RealVal(6), proQF: txNext >= tx, proQS: m == RealVal(1)}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Railroad()
    stlObject = STLHandler(model, testcaseSTL)
    stlObject.generateSTL()


