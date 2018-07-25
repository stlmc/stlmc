import os, sys, io
from .tcNon import testcaseSTL
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
CLO = RealVal(2)

V = -RealVal(5)


class RailroadPoly(Model):
    def __init__(self):
        mf = Bool('mf')
        ms = Bool('ms')
        mt = Bool('mt')
        tx = Real('tx')   #train position
        bx = Real('bx')   #angualr 90: open, 0: close
        vx = Real('vx')
        constvx = Real('constvx')
        
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        mtNext = NextVar(mt)
        txNext = NextVar(tx)
        bxNext = NextVar(bx)
        vxNext = NextVar(vx)
        constvxNext = NextVar(constvx)

        proPF = Bool('pf')
        proPS = Bool('ps')
        proQF = Bool('qf')
        proQS = Bool('qs')
        mode = {}
        vars = {tx: (-20, 100), bx: (0, 90)}
        init = And(And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)), bx >= RealVal(0), bx < RealVal(1), tx >= RealVal(60), tx <= RealVal(70), vx <= RealVal(0.1), vx >= RealVal(0), constvx == vx)

        flow = {And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)): {tx: V, bx: constvx, vx: RealVal(0), constvx : RealVal(0)}, \
                And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(True)): {tx: V, bx: constvx, vx: RealVal(5), constvx : RealVal(0)}, \
                And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(False)): {tx: V, bx: constvx, vx: RealVal(10), constvx : RealVal(0)}, \
                And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(True)): {tx: V, bx: constvx, vx: -RealVal(5), constvx : RealVal(0)}, \
                And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False)): {tx: V, bx: constvx, vx: RealVal(0), constvx : RealVal(0)}, \
                And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(True)): {tx: V, bx: constvx, vx: RealVal(0), constvx : RealVal(0)}}


        inv = {And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)): And(tx >= RealVal(40), tx <= RealVal(95), bx >= RealVal(0), bx < RealVal(90)), \
               And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(True)): And(tx < RealVal(50), tx >= RealVal(20), bx > RealVal(0), bx <= RealVal(90)), \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(False)): And(tx < RealVal(30), tx >= RealVal(10), bx > RealVal(0), bx <= RealVal(90)), \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(True)): And(tx < RealVal(15), tx >= RealVal(5), bx >= RealVal(0), bx < RealVal(90)), \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False)): And(bx < RealVal(8)), \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(True)): bxNext == bx}


        jump = {And(And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)), tx < RealVal(50), tx >= RealVal(40)): And(And(mfNext == BoolVal(False), msNext == BoolVal(False), mtNext == BoolVal(True)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(True)), tx < RealVal(30), tx >= RealVal(20)): And(And(mfNext == BoolVal(False), msNext == BoolVal(True), mtNext == BoolVal(False)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(False)), tx < RealVal(10), tx >= RealVal(5), bx <= RealVal(85)): And(And(mfNext == BoolVal(False), msNext == BoolVal(True), mtNext == BoolVal(True)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(False)), bx > RealVal(85)): And(And(mfNext == BoolVal(True), msNext == BoolVal(False), mtNext == BoolVal(True)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(True)), tx < RealVal(5)): And(And(mfNext == BoolVal(False), msNext == BoolVal(True), mtNext == BoolVal(True)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(True)), bx < RealVal(1)):  And(And(mfNext == BoolVal(True), msNext == BoolVal(False), mtNext == BoolVal(True)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False)), tx < -RealVal(5), tx >= -RealVal(10)): And(And(mfNext == BoolVal(False), msNext == BoolVal(False), mtNext == BoolVal(False)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == (RealVal(85) + tx))}

        goal = tx <= RealVal(0)

        prop = {proPF : And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False)), proPS: tx <= RealVal(0), proQF: bx >= RealVal(80), proQS: bx <= RealVal(40)}

        super().__init__(mode, vars, init, flow, inv, jump, prop, 1, testcaseSTL, "PolyRailroadReport", goal)


if __name__ == '__main__':
    model = Railroad()
    stlObject = STLHandler(model)
    for i in range(len(model.stl)):
        formula = parseFormula(model.stl[i])
        print(formula)
        for j in range(1,2):
            (a, b, c, d) = model.modelCheck(formula, j)
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

