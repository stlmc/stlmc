import os, sys, io
from .tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
from core.STLHandler import *
import time

K1 = RealVal(0.015)
K2 = RealVal(0.045)
h1 = RealVal(100.0)
h2 = RealVal(200.0)
c = RealVal(0.01)

gT = RealVal(20)

class Thermostat(Model):
    def __init__(self):
        mf = Bool('mf')
        ms = Bool('ms')
        fx = Real('fx')
        sx = Real('sx')

        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        proQF = Bool('qf')
        proMF = Bool('promf')

        proPS = Bool('ps')
        proMS = Bool('proms')

        mode = {}
        vars = {fx: (-20, 100), sx: (-20, 100)}
        init = And(And(mf == BoolVal(False), ms == BoolVal(False)), fx >= gT - RealVal(0.1), fx <= gT + RealVal(0.1), sx >= gT + RealVal(3), sx <= gT + RealVal(3.5))

        fxOff = -RealVal(0.4) 
        fxOn = RealVal(0.7)
        sxOff = -RealVal(0.6)
        sxOn = RealVal(1)

        flow = {And(mf == BoolVal(False), ms == BoolVal(False)): {fx: fxOff, sx: sxOff}, \
                And(mf == BoolVal(False), ms == BoolVal(True)): {fx: fxOff, sx: sxOn}, \
                And(mf == BoolVal(True), ms == BoolVal(False)): {fx: fxOn, sx: sxOff}, \
                And(mf == BoolVal(True), ms == BoolVal(True)): {fx: fxOn, sx: sxOn}}
        inv = {And(mf == BoolVal(False), ms == BoolVal(False)): And(fx > RealVal(0), sx > RealVal(0)), \
               And(mf == BoolVal(False), ms == BoolVal(True)): And(fx > RealVal(0), sx < RealVal(50)), \
               And(mf == BoolVal(True), ms == BoolVal(False)): And(fx < RealVal(50), sx > RealVal(0)), \
               And(mf == BoolVal(True), ms == BoolVal(True)):  And(fx < RealVal(50), sx < RealVal(50))}
        '''
        inv = {And(mf == BoolVal(False), ms == BoolVal(False)): BoolVal(True), \
               And(mf == BoolVal(False), ms == BoolVal(True)): BoolVal(True), \
               And(mf == BoolVal(True), ms == BoolVal(False)): BoolVal(True), \
               And(mf == BoolVal(True), ms == BoolVal(True)):  BoolVal(True)}
        '''
        jump = {And((fx > ((fx + sx) / RealVal(2))), (sx > ((fx + sx) / RealVal(2)))):  And(mfNext == BoolVal(False), msNext == BoolVal(False), fxNext == fx, sxNext == sx), \
                And((fx <= ((fx + sx) / RealVal(2))), (sx <= ((fx + sx) / RealVal(2)))): And(mfNext == BoolVal(True), msNext == BoolVal(True), fxNext == fx, sxNext == sx), \
                And((fx > ((fx + sx) / RealVal(2))), (sx <= ((fx + sx) / RealVal(2))))    : And(mfNext == BoolVal(False), msNext == BoolVal(True), fxNext == fx, sxNext == sx), \
                And((fx <= ((fx + sx) / RealVal(2))), (sx > ((fx + sx) / RealVal(2)))): And(mfNext == BoolVal(True), msNext == BoolVal(False), fxNext == fx, sxNext == sx)}


        prop = {(proQF): (fx > ((fx + sx) / RealVal(2))), proMF: And(mf == BoolVal(False), ms == BoolVal(False)), \
               proPS: (sx <= (((fx + sx) / RealVal(2)) - RealVal(1))), proMS: And(mf == BoolVal(True), ms == BoolVal(True))}

        goal = (fx > ((fx + sx) / RealVal(2)))

        super().__init__(mode, vars, init, flow, inv, jump, prop, 1, testcaseSTL, "LinearThermostatReport", goal)


if __name__ == '__main__':
    model = Thermostat()
    stlObject = STLHandler(model)
    model.reach(1)
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
           # print(s.to_smt2())
            stime1 = time.process_time()
            checkresult = s.check()
            etime1 = time.process_time()
            print(str(j) + ":  " + str(checkresult) + " " + str(etime1 - stime1))











