import os, sys, io
from .tcNon import testcaseSTL
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
from core.dRealHandler import *
from core.z3Handler import *
from model import *
from core.STLHandler import *
import time

gH = RealVal(5.0)
g = RealVal(9.806)
a = RealVal(0.5)

A1 = RealVal(8.0)
A2 = RealVal(9.0)
q1 = RealVal(5.0)
q2 = RealVal(3.0)

class WatertankPoly(Model):
    def __init__(self):
        mf = Bool('mf')
        ms = Bool('ms')
        fx = Real('fx')
        sx = Real('sx')
        constfx = Real('constfx')
        constsx = Real('constsx')

        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        constfxNext = NextVar(constfx)
        constsxNext = NextVar(constsx)
        proPF = Bool('pf')
        proQF = Bool('qf')
        proMF1 = Bool('promf1')
        proMF2 = Bool('promf2')
        proZF = Bool('zf')

        mode = {}
        vars = {fx: (0, 10), sx: (0, 10), constfx: (0, 10), constsx: (0, 10)}
        init = And(mf == BoolVal(True), ms == BoolVal(True), fx >= gH - RealVal(0.1), fx <= gH + RealVal(0.1), sx >= gH - RealVal(0.1), sx <= gH + RealVal(0.1), And(constfx == fx, constsx == sx))

        fxOff = -a * RealVal(2) * g / RealVal(2) * constfx / (RealVal(2) * A1) 
        fxOn = (q1 - a * RealVal(2) * g / RealVal(2) * constfx) / (RealVal(2) * A1)
        sxOff = (a * RealVal(2) * g / RealVal(2) * (constfx - constsx)) / (RealVal(2) * A2)
        sxOn = (q2 + a * RealVal(2) * g / RealVal(2) * (constfx - constsx)) / (RealVal(2) * A2)

        flow = {And(mf == BoolVal(False), ms == BoolVal(False)): {fx: fxOff, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                And(mf == BoolVal(False), ms == BoolVal(True)): {fx: fxOff, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}, \
                And(mf == BoolVal(True), ms == BoolVal(False)): {fx: fxOn, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                And(mf == BoolVal(True), ms == BoolVal(True)): {fx: fxOn, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}}

        inv = {And(mf == BoolVal(False), ms == BoolVal(False)): And(fx > RealVal(0), sx > RealVal(0)), \
               And(mf == BoolVal(False), ms == BoolVal(True)): And(fx > RealVal(0), sx <= A2), \
               And(mf == BoolVal(True), ms == BoolVal(False)): And(fx <= A1, sx > RealVal(0) ), \
               And(mf == BoolVal(True), ms == BoolVal(True)):  And(fx <= A1, sx <= A2)}

        jump = {And(fx < gH, sx < gH):  And(mfNext == BoolVal(True), msNext == BoolVal(True), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               And(fx < gH, sx >= gH):  And(mfNext == BoolVal(True), msNext == BoolVal(False), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               And(fx >= gH, sx < gH):  And(mfNext == BoolVal(False), msNext == BoolVal(True), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
               And(fx >= gH, sx >= gH):  And(mfNext == BoolVal(False), msNext == BoolVal(False), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx)}

        prop = {proPF: fx > (gH + RealVal(0.1)), (proQF): fx < RealVal(5), (proMF1): And(mf == BoolVal(True), ms == BoolVal(True)), proMF2: And(mf == BoolVal(True), ms == BoolVal(True)), proZF: fx < (gH - RealVal(0.1)) }

        goal = fx > (gH + RealVal(0.1))

        super().__init__(mode, vars, init, flow, inv, jump, prop, 0.1, testcaseSTL, "PolyWatertankReport", goal)


if __name__ == '__main__':
    model = Watertank()
    stlObject = STLHandler(model)
    for i in range(len(model.stl)):
        formula = parseFormula(model.stl[i])
        print(formula)
        for j in range(3):
            (a, b, c) = model.modelCheck(formula, j)
            z3model = [z3Obj(i) for i in a]
            z3partition = [z3Obj(i) for i in b]
            z3full = z3Obj(c)
            s = z3.Solver()
            const = z3model + z3partition + [z3full]
            s.add(const)
#        print(s.to_smt2())
            stime1 = time.process_time()
            checkresult = s.check()
            etime1 = time.process_time()
            print(str(j) + ":  " + str(checkresult) + " " + str(etime1 - stime1))












