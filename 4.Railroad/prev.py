import os, sys, io
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.interface import *
from core.dRealHandler import *
from model import *

FAR = RealVal(1)
APPROACH = RealVal(2)
NEAR = RealVal(3)
PAST = RealVal(4)

OPEN = RealVal(1)
OPENING = RealVal(2)
CLOSE = RealVal(3)
CLOSING = RealVal(4)

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
        mode = [tm, bm]
        vars = {tx: (-20, 100), bx: (0, 90)}
        init = And(tm == FAR, bm == CLOSE, bx == RealVal(0), tx >= RealVal(5), tx <= RealVal(8))

        flow = {Implies(tm == FAR, bm == CLOSE): {tx: V, bx: RealVal(0)}, \
                Implies(tm == APPROACH, bm == OPENING): {tx: V, bx: RealVal(5)}, \
                Implies(tm == NEAR, bm == OPEN): {tx: V, bx: RealVal(0)}, \
                Implies(tm == PAST, bm == CLOSING): {tx: V, bx: -RealVal(5)}}

        inv = {tm == FAR: And(tx >= RealVal(40), tx <= RealVal(95)), \
               bm == CLOSE: bx == RealVal(0), \
               tm == APPROACH: And(tx < RealVal(40), tx >= RealVal(20)), \
               bm == OPENING: And(bx > RealVal(0), bx < RealVal(90)), \
               tm == NEAR: And(tx < RealVal(20), tx >= RealVal(5)), \
               bm == OPEN: bx == RealVal(90), \
               tm == PAST: And(tx < RealVal(5), tx >= -RealVal(10)), \
               bm == CLOSING: And(bx > RealVal(0), bx < RealVal(90))} 
              
        jump = {And(tx < RealVal(40), tx >= RealVal(20)): And(tmNext == APPROACH, bmNext == bm, txNext == tx, bxNext == bx), \
                And(tx < RealVal(20), tx >= RealVal(5)): And(tmNext == NEAR, bmNext == bm, txNext == tx, bxNext == bx), \
                And(tx < RealVal(5), tx >= -RealVal(10)): And(tmNext == PAST, bmNext == bm, bxNext == bx, txNext == RealVal(95)), \
                And(tx >= RealVal(40), tx <= RealVal(95)): And(tmNext == FAR, bmNext == bm, bxNext == bx,  txNext == tx), \
                And(bm == CLOSING, bx == RealVal(0)): And(bmNext == CLOSE, bxNext == bx, tmNext == tm, txNext == tx), \
                And(bm == OPENING, bx == RealVal(90)): And(bmNext == OPEN, bxNext == bx, tmNext == tm, txNext == tx), \
                And(bm == OPEN, bx < RealVal(90)): And(bmNext == CLOSING, bxNext == bx, tmNext == tm, txNext == tx), \
                And(bm == CLOSE, bx > RealVal(0)): And(bmNext == OPENING, bxNext == bx, tmNext == tm, txNext == tx)}

        prop = {}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Railroad()
    const = model.reach(2)

    output = io.StringIO()
    printObject = dRealHandler(const, output, model.variables, model.flowDict)
    printObject.callAll()
    f = open('test.smt2', 'w')
    f.write(output.getvalue())
    f.close()

    s = z3.Solver()
    for i in range(len(const)):
        s.add(const[i].z3Obj())
#    print(s.to_smt2())
    print(s.check())
#    print(s.model())
