import os, sys, time
from .carLinearSTL import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from stlMC import *

#STL
#from carLinearSTL import testcaseSTL

# reachability goal
goal = ((Real('x2') - Real('x1')) >= RealVal(4))

# some constants 
V1Fast = RealVal(65)
V1Slow = RealVal(25)
V1Keep = RealVal(30)
V2Fast = RealVal(60)
V2Slow = RealVal(35)
V2Keep = RealVal(40)

class CarLinear(Model):
    def __init__(self):
        # modes
        mf = Bool('mf')
        ms = Bool('ms')
        mt = Bool('mt')

        # variables
        x1 = Real('x1')
        x2 = Real('x2')

        # flow conditions
        flow = {\
               And(Not(mf), Not(ms), Not(mt)): {x1: V1Fast, x2: V2Fast}, \
               And(Not(mf), Not(ms), mt): {x1: V1Fast, x2: V2Keep}, \
               And(Not(mf), ms, Not(mt)): {x1: V1Keep, x2: V2Fast}, \
               And(Not(mf), ms, mt): {x1: V1Keep, x2: V2Slow}, \
               And(mf, Not(ms), Not(mt)): {x1: V1Slow, x2: V2Fast}, \
               And(mf, Not(ms), mt): {x1: V1Slow, x2: V2Slow}}

        # initial conditions
        init = And(And(Not(mf), Not(ms), Not(mt)), x1 >= RealVal(0), x1 <= RealVal(1), x2 <= RealVal(10), x2 >= RealVal(3))

        # set the interval bound to the variables 
        vars = {x1: (0, 1000), x2: (0, 1000)} 
        # invariant conditions
        inv = {And(Not(mf), Not(ms), Not(mt)): x2 >= x1, \
               And(Not(mf), Not(ms), mt): x2 >= x1, \
               And(Not(mf), ms, Not(mt)): x2 >= x1, \
               And(Not(mf), ms, mt): x2 >= x1, \
               And(mf, Not(ms), Not(mt)): x2 >= x1, \
               And(mf, Not(ms), mt): x2 >= x1}

        # jump conditions
        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        mtNext = NextVar(mt)
        x1Next = NextVar(x1)
        x2Next = NextVar(x2)

        jump = {\
                And((x2 - x1) >= RealVal(2), (x2 - x1) < RealVal(3)): \
                And(And(Not(mfNext), Not(msNext), Not(mtNext), x1Next == x1, x2Next == x2)), \
                And((x2 - x1) >= RealVal(3), (x2 - x1) < RealVal(4)): \
                And(And(Not(mfNext), Not(msNext), mtNext), x1Next == x1, x2Next == x2), \
                And((x2 - x1) >= RealVal(1), (x2 - x1) < RealVal(2)): \
                And(And(Not(mfNext), msNext, Not(mtNext), x1Next == x1, x2Next == x2)), \
                And((x2 - x1) >= RealVal(4), (x2 - x1) < RealVal(5)): \
                And(And(Not(mfNext), msNext, mtNext), x1Next == x1, x2Next == x2), \
                x2 - x1 <  RealVal(1): \
                And(And(mfNext, Not(msNext), Not(mtNext)), x1Next == x1, x2Next == x2), \
                x2 - x1 >= RealVal(5): \
                And(And(mfNext, Not(msNext), mtNext), x1Next == x1, x2Next == x2)}


        # STL propositions
        proBFL = Bool('bfonel')
        proBFR = Bool('bfoner')
        proF = Bool('fone')
        proS = Bool('ftwo')
        proTL = Bool('fthreep')
        proTR = Bool('fthreeq')

        prop = {proBFL: ((x2 - x1) <= RealVal(4)), proBFR: And(Not(mf), ms, Not(mt)), \
                proF: x2 > x1, \
                proS: And(Not(mf), ms, mt), \
                proTL: ((x2 - x1) >= RealVal(4.5)), proTR: And(mf, Not(ms), Not(mt))}

        super().__init__(vars, init, flow, inv, jump, prop, "QF_LRA")



