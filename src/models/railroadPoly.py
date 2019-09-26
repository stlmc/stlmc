import os, sys
from stlMC import *
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))

# STL
from .railroadSTL import testcaseSTL

# reachability goal
goal = Real('tx') < RealVal(0.5)

# some constants
V = -RealVal(5)

class RailroadPoly(Model):
    def __init__(self):
        # modes
        mf = Bool('ms')
        ms = Bool('mt')

        # variables
        tx = Real('tx')   #train position
        bx = Real('bx')   #angualr 90: open, 0: close
        vx = Real('vx')
        constvx = Real('constvx')


        # flow conditions
        flow = {\
                And(Not(mf), Not(ms)): \
                {tx: V, bx: constvx, vx: RealVal(0), constvx : RealVal(0)}, \
                And(Not(mf), ms): \
                {tx: V, bx: constvx, vx: RealVal(5), constvx : RealVal(0)}, \
                And(mf, Not(ms)): \
                {tx: V, bx: constvx, vx: RealVal(10), constvx : RealVal(0)}, \
                And(mf, ms): \
                {tx: V, bx: constvx, vx: -RealVal(5), constvx : RealVal(0)}}

        # initial conditions
        init = And(And(Not(mf), Not(ms)), bx >= RealVal(0), bx < RealVal(1), tx >= RealVal(60), tx <= RealVal(70), vx <= RealVal(0.1), vx >= RealVal(0), constvx == vx)

        # set the interval bound to the variables
        vars = {tx: (-20, 100), bx: (0, 90), vx: (-50, 50)}
        # invariant conditions
        inv = {\
               And(Not(mf), Not(ms)): \
               BoolVal(True), \
               And(Not(mf), ms): \
               BoolVal(True), \
               And(mf, Not(ms)): \
               BoolVal(True), \
               And(mf, ms): \
               And(bx > RealVal(80), bx < RealVal(90))}

       # jump conditions
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        txNext = NextVar(tx)
        bxNext = NextVar(bx)
        vxNext = NextVar(vx)
        constvxNext = NextVar(constvx)

        jump = {\
                And(tx < RealVal(50), tx >= RealVal(40)): \
                And(And(Not(mfNext), msNext), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(tx < RealVal(30), tx >= RealVal(20)): \
                And(And(mfNext, Not(msNext)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(tx >= -RealVal(5), tx <= RealVal(0)): \
                And(And(mfNext, msNext), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == tx), \
                And(tx < -RealVal(5), tx >= -RealVal(10)): \
                And(And(Not(mfNext), Not(msNext)), vxNext == vx, constvxNext == vx, bxNext == bx, txNext == (RealVal(100) + tx))}


        # STL propositions
        proZero = Bool('reachability')
        proBFL = Bool('bfonel')
        proFR = Bool('foneq')

        prop = {proZero: tx < RealVal(0), \
                proBFL: bx >= RealVal(80), \
                proFR: bx < RealVal(60)}


        super().__init__(vars, init, flow, inv, jump, prop, "QF_NRA")



