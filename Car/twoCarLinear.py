import os, sys, io
from .tcLinear import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
from core.STLHandler import *
import time

L1 = RealVal(1)
L2 = RealVal(1.5)
V1Acc = RealVal(4.0)
V1Dec = RealVal(0.3)
V2Acc = RealVal(3.0)
V2Dec = RealVal(0.5)
Keep = RealVal(1)
#Acc: 1, Keep: 0, Dec: -1

class CarLinear(Model):
    def __init__(self):
        mf = Bool('mf')
        ms = Bool('ms')
        mt = Bool('mt')
        x1 = Real('x1')
        x2 = Real('x2')

        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        mtNext = NextVar(mt)
        x1Next = NextVar(x1)
        x2Next = NextVar(x2)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proMF = Bool('promf')

        vars = {x1: (0, 100), x2: (0, 100)}
        init = And(And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)), x1 >= RealVal(0), x1 <= RealVal(1), x2 <= RealVal(10), x2 >= RealVal(3))


        flow = {And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)): {x1: V1Acc, x2: V2Acc}, \
               And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(True)): {x1: V1Acc, x2: Keep}, \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(False)): {x1: Keep, x2: V2Acc}, \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(True)): {x1: Keep, x2: V2Dec}, \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False)): {x1: V1Dec, x2: V2Acc}, \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(True)): {x1: V1Dec, x2: V2Dec}}
  
        inv = {And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(False)): x2 >= x1, \
               And(mf == BoolVal(False), ms == BoolVal(False), mt == BoolVal(True)): x2 >= x1, \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(False)): x2 >= x1, \
               And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(True)): x2 >= x1, \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(False)): x2 >= x1, \
               And(mf == BoolVal(True), ms == BoolVal(False), mt == BoolVal(True)): x2 >= x1}


        jump = {And((x2 - x1) >= RealVal(2), (x2 - x1) < RealVal(3)): And(And(mfNext == BoolVal(False), msNext == BoolVal(False), mtNext == BoolVal(False), mtNext == BoolVal(False)), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(3), (x2 - x1) < RealVal(4)): And(And(mfNext == BoolVal(False), msNext == BoolVal(False), mtNext == BoolVal(True)), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(1), (x2 - x1) < RealVal(2)): And(And(mfNext == BoolVal(False), msNext == BoolVal(True), mtNext == BoolVal(False)), x1Next == x1, x2Next == x2), \
               And((x2 - x1) >= RealVal(4), (x2 - x1) < RealVal(5)): And(And(mfNext == BoolVal(False), msNext == BoolVal(True), mtNext == BoolVal(True)), x1Next == x1, x2Next == x2), \
               x2 - x1 <  RealVal(1): And(And(mfNext == BoolVal(True), msNext == BoolVal(False), mtNext == BoolVal(False)), x1Next == x1, x2Next == x2), \
               x2 - x1 >= RealVal(5): And(And(mfNext == BoolVal(True), msNext == BoolVal(False), mtNext == BoolVal(True)), x1Next == x1, x2Next == x2)}

        prop = {proPF : x2 - x1 <= RealVal(3), proQF: x2 - x1 < RealVal(4), proMF: And(mf == BoolVal(False), ms == BoolVal(True), mt == BoolVal(True)) }

        goal = ((x2 - x1) <= RealVal(3))

        super().__init__({}, vars, init, flow, inv, jump, prop, 1, testcaseSTL, "LinearCarReport", goal)


if __name__ == '__main__':
    model = Car()
    model.reach(10)
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
           # checkresult = s.check()
            etime1 = time.process_time()
            print(z3.simplify(z3.And(z3model)))









