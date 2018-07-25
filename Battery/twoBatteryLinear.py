import os, sys, io
from .tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
import math 
from core.STLHandler import *

K = RealVal(0.122)
C = RealVal(0.166)

#On: 1, Off: 0, Dead: -1

class BatteryLinear(Model):
    def __init__(self):
        mf = Bool('mf')
        ms = Bool('ms')
        mt = Bool('mt')
        d1 = Real('d1')
        d2 = Real('d2')
        g1 = Real('g1')
        g2 = Real('g2')

        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        mtNext = NextVar(mt)
        d1Next = NextVar(d1)
        d2Next = NextVar(d2)
        g1Next = NextVar(g1)
        g2Next = NextVar(g2)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proPZ = Bool('pz')
        proQZ = Bool('qz')
        proMT = Bool('mo')
        proMO = Bool('mt')
        proPS = Bool('ps')

        mode = {}
        vars = {d1: (-10, 10), d2: (-10, 10), g1: (-10, 10), g2: (-10, 10)}
        init = And(And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)), g1 == RealVal(8.5), d1 == RealVal(0), g2 == RealVal(7.5), d2 == RealVal(0))

        flow = {And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)): {d1: (RealVal(0.5) / C), d2: (RealVal(0.5) / C), g1: -RealVal(0.5), g2: -RealVal(0.5)}, \
               And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(True)): {d1: (RealVal(0.7) / C), d2: -C, g1: -RealVal(1), g2: RealVal(0)}, \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(False)): {d1: -C, d2: (RealVal(0.7) / C), g1: RealVal(0), g2: -RealVal(1)}, \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(True)): {d1: RealVal(0), d2: (RealVal(0.7) / C), g1: RealVal(0), g2: -RealVal(1)}, \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False)): {d1: (RealVal(0.7) / C), d2: RealVal(0), g1: -RealVal(1), g2: RealVal(0)}, \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(True)): {d1: RealVal(0), d2: RealVal(0), g1: RealVal(0), g2: RealVal(0)}}
  
        inv = {And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)): BoolVal(True), \
               And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(True)): BoolVal(True), \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(False)): BoolVal(True), \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(True)): BoolVal(True), \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False)): BoolVal(True), \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(True)): BoolVal(True)}

        jump = {And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(And(mfNext == BoolVal(False), msNext == BoolVal(False), mtNext == BoolVal(True)), d1Next == (d1 - K * g1), g1Next == g1, d2Next == (d2 - K * g2), g2Next == g2), \
               And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(And(mfNext == BoolVal(False), msNext == BoolVal(True), mtNext == BoolVal(False)), d1Next == (d1 - K * g1), g1Next == g1, d2Next == (d2 - K * g2), g2Next == g2), \
               And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(And(mfNext == BoolVal(False), msNext == BoolVal(True), mtNext == BoolVal(True)), d1Next == (d1 - K * g1), g1Next == g1, d2Next == (d2 - K * g2), g2Next == g2), \
               And(g1 <= (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(And(mfNext == BoolVal(False), msNext == BoolVal(True), mtNext == BoolVal(True)), d1Next == (d1 - K * g1), g1Next == g1, d2Next == (d2 - K * g2), g2Next == g2), \
               And(g1 > (RealVal(1) - C) * d1, g2 <= (RealVal(1) - C) * d2): And(And(mfNext == BoolVal(True), msNext == BoolVal(False), mtNext == BoolVal(False)), d1Next == (d1 - K * g1), g1Next == g1, d2Next == (d2 - K * g2), g2Next == g2), \
               And(g1 <= (RealVal(1) - C) * d1, g2 <= (RealVal(1) - C) * d2): And(And(mfNext == BoolVal(True), msNext == BoolVal(False), mtNext == BoolVal(True)), d1Next == (d1 - K * g1), g1Next == g1, d2Next == (d2 - K * g2), g2Next == g2)}

        prop = {proPS: g1 <= RealVal(1), proPF: And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(True)), proQF: g1 >= RealVal(0), proQZ: g2 >= RealVal(0), proMT: And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(True)), proMO: And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)), proPZ: And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False))}

        goal = g1 <= RealVal(1)


        super().__init__(mode, vars, init, flow, inv, jump, prop, 0.1, testcaseSTL, "LinearBatteryReport", goal)


if __name__ == '__main__':
    model = Battery()
    stlObject = STLHandler(model)
    for i in range(len(model.stl)):
        formula = parseFormula(model.stl[i])
        (a, b, c, d) = model.modelCheck(formula, 1)
        z3model = [z3Obj(i) for i in a]
        z3partition = [z3Obj(i) for i in b]
        z3full = z3Obj(c)
        s = z3.Solver()
        const = z3model + z3partition + [z3full]
        s.add(const)
        print(formula)
#        print(s.to_smt2())
        print(s.check())











