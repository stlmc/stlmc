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

        flow = {bm == CLOSE: {tx: V, bx: RealVal(0)}, \
                bm == OPENING: {tx: V, bx: RealVal(5)}, \
                bm == OPEN: {tx: V, bx: RealVal(0)}, \
                bm == CLOSING: {tx: V, bx: -RealVal(5)}}

        inv = { bm == CLOSE: And(tx >= RealVal(40), tx <= RealVal(95), bx == RealVal(0)), \
               bm == OPENING: And(tx < RealVal(40), tx >= RealVal(20), bx > RealVal(0), bx < RealVal(90)), \
               bm == OPEN: And(tx < RealVal(20), tx >= RealVal(5), bx == RealVal(90)), \
               bm == CLOSING: And(tx < RealVal(5), tx >= -RealVal(10), bx > RealVal(0), bx < RealVal(90))} 
              
        jump = {And(bm == CLOSING, bx == RealVal(0)): And(bxNext == bx, tmNext == tm, txNext == tx), \
                And(bm == OPENING, bx == RealVal(90)): And(bmNext == OPEN, bxNext == bx, txNext == tx), \
                And(bm == OPEN, bx < RealVal(90)): And(bmNext == CLOSING, bxNext == bx, txNext == tx), \
                And(bm == CLOSE, bx > RealVal(0)): And(bmNext == OPENING, bxNext == bx, txNext == tx)}

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
