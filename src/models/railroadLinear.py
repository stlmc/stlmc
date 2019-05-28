import os, sys
from stlMC import *

sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))

# STLs
from .railroadSTL import testcaseSTL

# reachability goal
goal = Real('tx') < RealVal(0.5)

# some constant
V = -RealVal(5)

class RailroadLinear(Model):
    def __init__(self):
        # modes
        mf = Bool('mf')
        ms = Bool('ms')

        # variables
        tx = Real('tx')   #train position
        bx = Real('bx')   #angualr 90: open, 0: close
        
        # flow conditions
        flow = {\
                And(Not(mf), Not(ms)): {tx: V, bx: RealVal(0)}, \
                And(Not(mf), ms): {tx: V, bx: RealVal(5)}, \
                And(mf, Not(ms)): {tx: V, bx: RealVal(10)}, \
                And(mf, ms): {tx: V, bx: -RealVal(5)}}

        # initial conditions
        init = And(And(Not(mf), Not(ms)), bx >= RealVal(0), bx < RealVal(1), tx >= RealVal(60), tx <= RealVal(70))


        # set the interval bound to the variables
        vars = {tx: (-20, 100), bx: (0, 90)}
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

        jump = {\
                And(tx < RealVal(50), tx >= RealVal(40)): \
                And(And(Not(mfNext), msNext), bxNext == bx, txNext == tx), \
                And(tx < RealVal(30), tx >= RealVal(20)): \
                And(And(mfNext, Not(msNext)), bxNext == bx, txNext == tx), \
                And(tx >= -RealVal(5), tx <= RealVal(0)): \
                And(And(mfNext, msNext), bxNext == bx, txNext == tx), \
                And(tx < -RealVal(5), tx >= -RealVal(10)): \
                And(And(Not(mfNext), Not(msNext)), bxNext == bx, txNext == (RealVal(100) + tx))}

        # STL propositions
        proZero = Bool('reachability')
        proBFL = Bool('bfonel')
        proFR = Bool('foneq')

        prop = {proZero: tx < RealVal(0), \
                proBFL: bx >= RealVal(80), \
                proFR: bx < RealVal(60)}


        super().__init__(vars, init, flow, inv, jump, prop, "QF_LRA")




