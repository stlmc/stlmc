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
        constfx = Real('constfx')
        constsx = Real('constsx')

        mfNext = NextVar(mf)
        msNext = NextVar(ms)
        fxNext = NextVar(fx)
        sxNext = NextVar(sx)
        constfxNext = NextVar(constfx)
        constsxNext = NextVar(constsx)
        proQF = Bool('qf')
        proMF = Bool('promf')

        proPS = Bool('ps')
        proMS = Bool('proms')

        mode = {}
        vars = {fx: (-20, 100), sx: (-20, 100), constfx: (-20, 100), constsx: (-20, 100)}
        init = And(And(mf == BoolVal(False), ms == BoolVal(False)), fx >= gT - RealVal(1), fx <= gT + RealVal(1), sx >= gT - RealVal(1), sx <= gT + RealVal(1), And(constfx == fx, constsx == sx))

        fxOff = -K1 * ((RealVal(1) - RealVal(2) * c) * constfx + c * constsx) 
        fxOn = K1 * (h1 -((RealVal(1) - RealVal(2) * c) * constfx + c * constsx))
        sxOff = -K2 * ((RealVal(1) - RealVal(2) * c) * constsx + c * constfx)
        sxOn = K2 * (h2 -((RealVal(1) - RealVal(2) * c) * constsx + c * constfx))

        flow = {And(mf == BoolVal(False), ms == BoolVal(False)): {fx: fxOff, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                And(mf == BoolVal(False), ms == BoolVal(True)): {fx: fxOff, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}, \
                And(mf == BoolVal(True), ms == BoolVal(False)): {fx: fxOn, sx: sxOff, constfx: RealVal(0), constsx: RealVal(0)}, \
                And(mf == BoolVal(True), ms == BoolVal(True)): {fx: fxOn, sx: sxOn, constfx: RealVal(0), constsx: RealVal(0)}}

        inv = {And(mf == BoolVal(False), ms == BoolVal(False)): And(fx > RealVal(10), sx > RealVal(10)), \
               And(mf == BoolVal(False), ms == BoolVal(True)): And(fx > RealVal(10), sx < RealVal(30)), \
               And(mf == BoolVal(True), ms == BoolVal(False)): And(fx < RealVal(30), sx > RealVal(10)), \
               And(mf == BoolVal(True), ms == BoolVal(True)):  And(fx < RealVal(30), sx < RealVal(30))}

        jump = {And(fx > gT, sx > gT):  And(mfNext == BoolVal(False), msNext == BoolVal(False), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
                     And(fx <= gT, sx <= gT): And(mfNext == BoolVal(True), msNext == BoolVal(True), fxNext == fx, constfxNext == fx, sxNext == sx, constsxNext == sx), \
                     And(fx > gT, sx <= gT): And(mfNext == BoolVal(False), msNext == BoolVal(True), fxNext == fx, sxNext == sx, constsxNext == sx, constfxNext == fx), \
                     And(fx <= gT, sx > gT): And(mfNext == BoolVal(True), msNext == BoolVal(False), fxNext == fx, sxNext == sx, constfxNext == fx, constsxNext == sx)}


        prop = {(proQF): fx >  gT + RealVal(1), proMF: And(mf == BoolVal(False), ms == BoolVal(False)), \
               proPS: sx <= gT, proMS: And(mf == BoolVal(True), ms == BoolVal(True))}

        goal = fx > (gT + RealVal(1))

        super().__init__(mode, vars, init, flow, inv, jump, prop, 1, testcaseSTL, "ThermostatReport", goal)


if __name__ == '__main__':
    model = Thermostat()
    stlObject = STLHandler(model)
    for i in range(len(model.stl)):
        formula = parseFormula(model.stl[i])
        print(formula)
        for j in range(1,11):
            (a, b, c) = model.modelCheck(formula, j)
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











