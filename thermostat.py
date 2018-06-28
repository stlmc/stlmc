from interface import *

gT = RealVal(20)
LB = RealVal(16)
UB = RealVal(24)
MAX = RealVal(30)
MIN = RealVal(10)
S1 = RealVal(5)
S2 = RealVal(7)
S3 = RealVal(6)
H1 = RealVal(3)
H2 = RealVal(5)
H3 = RealVal(2)
D1 = RealVal(2)
D2 = RealVal(2)

class Thermostat:
    qOn = BoolVal(True)
    qOff = BoolVal(False)

    def reach(self, ts):
        k = len(ts) - 1
        qf   = [Bool("mf_%s"%i)   for i in range(k+1)]
        qs   = [Bool("ms_%s"%i)   for i in range(k+1)]
        qt   = [Bool("mt_%s"%i)   for i in range(k+1)]

        x1 = stateDeclare('fx', k)
        x2 = stateDeclare('sx', k)
        x3 = stateDeclare('tx', k)

        prPF = [Bool("pf_%s"%i)  for i in range(k)] # pf holds if fx <= 17
        prQF = [Bool("qf_%s"%i)  for i in range(k)] # qf holds if fx >= 20

        prPS = [Bool("ps_%s"%i)  for i in range(k)] # ps holds if sx <= 17
        prQS = [Bool("qs_%s"%i)  for i in range(k)] # qs holds if sx >= 20

        prPT = [Bool("pt_%s"%i)  for i in range(k)] # pt holds if tx <= 17
        prQT = [Bool("qt_%s"%i)  for i in range(k)] # qt holds if tx >= 20
        
        fxOff = -S1 * (Real('const' + x1.id) - (D1 * Real('const' + x2.id)))
        fxOn = S1 * (H1 -(Real('const' + x1.id) - (D1 * Real('const' + x2.id))))
        sxOff = -S2 * (Real('const' + x2.id) -(D1 * Real('const' + x1.id) + D2 * Real('const' + x3.id)))
        sxOn = S2 * (H2 - (Real('const' + x2.id) - (D1 * Real('const' + x1.id) + D2 * Real('const' + x3.id))))
        txOff = -S3 * (Real('const' + x3.id) - (D2 * Real('const' + x2.id)))
        txOn = S3 * (H3 - (Real('const' + x3.id) - (D2 * Real('const' + x2.id))))

        flow_1 = {x1.id: fxOff, x2.id: sxOff, x3.id: txOff, ('const' + x1.id): RealVal(0), ('const' + x2.id): RealVal(0), ('const' + x3.id): RealVal(0)}
        flow_2 = {x1.id: fxOff, x2.id: sxOff, x3.id: txOn, ('const' + x1.id): RealVal(0), ('const' + x2.id): RealVal(0), ('const' + x3.id): RealVal(0)}
        flow_3 = {x1.id: fxOff, x2.id: sxOn, x3.id: txOff, ('const' + x1.id): RealVal(0), ('const' + x2.id): RealVal(0), ('const' + x3.id): RealVal(0)}
        flow_4 = {x1.id: fxOff, x2.id: sxOn, x3.id: txOn, ('const' + x1.id): RealVal(0), ('const' + x2.id): RealVal(0), ('const' + x3.id): RealVal(0)}
        flow_5 = {x1.id: fxOn, x2.id: sxOff, x3.id: txOff, ('const' + x1.id): RealVal(0), ('const' + x2.id): RealVal(0), ('const' + x3.id): RealVal(0)}
        flow_6 = {x1.id: fxOn, x2.id: sxOff, x3.id: txOn, ('const' + x1.id): RealVal(0), ('const' + x2.id): RealVal(0), ('const' + x3.id): RealVal(0)}
        flow_7 = {x1.id: fxOn, x2.id: sxOn, x3.id: txOff, ('const' + x1.id): RealVal(0), ('const' + x2.id): RealVal(0), ('const' + x3.id): RealVal(0)}
        flow_8 = {x1.id: fxOn, x2.id: sxOn, x3.id: txOn, ('const' + x1.id): RealVal(0), ('const' + x2.id): RealVal(0), ('const' + x3.id): RealVal(0)}
        
        ODE_1 = ODE(1, flow_1)
        ODE_2 = ODE(2, flow_2)
        ODE_3 = ODE(3, flow_3)
        ODE_4 = ODE(4, flow_4)
        ODE_5 = ODE(5, flow_5)
        ODE_6 = ODE(6, flow_6)
        ODE_7 = ODE(7, flow_7)
        ODE_8 = ODE(8, flow_8)

        defineODE = [ODE_1, ODE_2, ODE_3, ODE_4, ODE_5, ODE_6, ODE_7, ODE_8]

        # reachability
        const = []
        const.append(self.init(qf[0], qs[0], qt[0], x1.start[0], x2.start[0], x3.start[0]))

        const.append(ts[0] <= RealVal(0))
        
        for i in range(1):
            const.append(self.flow(qf[i], qs[i], qt[i], [x1.start[i], x2.start[i], x3.start[i]], [x1.end[i], x2.end[i], x3.end[i]], ts[i+1] - ts[i], defineODE))
            const.append(self.jump(qf[i], qs[i], qt[i], x1.end[i], x2.end[i], x3.end[i], qf[i+1], qs[i+1], qt[i+1], x1.start[i+1], x2.start[i+1], x3.start[i+1]))
            const.append(self.inv(qf[i], qs[i], qt[i], [x1.id, x2.id, x3.id], [x1.start[i], x2.start[i], x3.start[i]], [x1.end[i], x2.end[i], x3.end[i]], ts[i+1] - ts[i]))

        variables = []
        for i in range(len(const)):
            variables += const[i].getVars()
        variables =removeDup(variables)

        return const 

    def inv(self, qf, qs, qt, variables, start, end, time):
        startDict = {}
        endDict = {}
        for i in range(len(variables)):
            startDict[variables[i]] = start[i]
            endDict[variables[i]] = end[i]
        x1var = Real(variables[0])
        x2var = Real(variables[1])
        x3var = Real(variables[2])
        invFFF  = Implies(And(qf == self.qOff, qs == self.qOff, qt == self.qOff), Forall(1, time, And(x1var > RealVal(10), x2var > RealVal(10), x3var > RealVal(10)), startDict, endDict))
        invFFO  = Implies(And(qf == self.qOff, qs == self.qOff, qt == self.qOn), Forall(2, time, And(x1var > RealVal(10), x2var > RealVal(10), x3var < RealVal(30)), startDict, endDict))
        invFOF  = Implies(And(qf == self.qOff, qs == self.qOn, qt == self.qOff), Forall(3, time, And(x1var > RealVal(10), x2var < RealVal(30), x3var > RealVal(30)), startDict, endDict))
        invFOO  = Implies(And(qf == self.qOff, qs == self.qOn, qt == self.qOn), Forall(4, time, And(x1var > RealVal(10), x2var < RealVal(30), x3var < RealVal(30)), startDict, endDict))
        invOFF  = Implies(And(qf == self.qOn, qs == self.qOff, qt == self.qOff), Forall(5, time, And(x1var < RealVal(30), x2var > RealVal(10), x3var > RealVal(10)), startDict, endDict))
        invOFO  = Implies(And(qf == self.qOn, qs == self.qOff, qt == self.qOn), Forall(6, time, And(x1var < RealVal(30), x2var > RealVal(10), x3var < RealVal(30)), startDict, endDict))
        invOOF  = Implies(And(qf == self.qOn, qs == self.qOn, qt == self.qOff), Forall(7, time, And(x1var < RealVal(30), x2var < RealVal(30), x3var > RealVal(10)), startDict, endDict))
        invOOO  = Implies(And(qf == self.qOn, qs == self.qOn, qt == self.qOn), Forall(8, time, And(x1var < RealVal(30), x2var < RealVal(30), x3var < RealVal(30)), startDict, endDict)) 
        s = z3.Solver()
        s.add(invFOF.z3Obj())
        print(s.to_smt2())
        return And(invFFF, invFFO, invFOF, invFOO, invOFF, invOFO, invOOF, invOOO)

    def flow(self, qf, qs, qt, start, end, time, ODElist):
        toFFF  = Implies(And(qf == self.qOff, qs == self.qOff, qt == self.qOff), Integral(end, start, time, ODElist[0]))
        toFFO  = Implies(And(qf == self.qOff, qs == self.qOff, qt == self.qOn), Integral(end, start, time, ODElist[1]))
        toFOF  = Implies(And(qf == self.qOff, qs == self.qOn, qt == self.qOff), Integral(end, start, time, ODElist[2]))
        toFOO  = Implies(And(qf == self.qOff, qs == self.qOn, qt == self.qOn), Integral(end, start, time, ODElist[3]))
        toOFF  = Implies(And(qf == self.qOn, qs == self.qOff, qt == self.qOff), Integral(end, start, time, ODElist[4]))
        toOFO  = Implies(And(qf == self.qOn, qs == self.qOff, qt == self.qOn), Integral(end, start, time, ODElist[5]))
        toOOF  = Implies(And(qf == self.qOn, qs == self.qOn, qt == self.qOff), Integral(end, start, time, ODElist[6]))
        toOOO  = Implies(And(qf == self.qOn, qs == self.qOn, qt == self.qOn), Integral(end, start, time, ODElist[7]))
        s = z3.Solver()
        s.add(toFOF.z3Obj())
#        print(s.to_smt2())
#        print(str(toFOF))
        return And(toFFF, toFFO, toFOF, toFOO, toOFF, toOFO, toOOF, toOOO)

    def init(self, fs, ss, ts, fv0, sv0, tv0):
        return And(And(fs == self.qOff, ss == self.qOff, ts == self.qOff), fv0 >= gT - RealVal(1), fv0 <= gT + RealVal(1), sv0 >= gT - RealVal(1), sv0 <= gT + RealVal(1), tv0 >= gT - RealVal(1), tv0 <= gT + RealVal(1))

    def jump(self, qf, qs, qt, fx, sx, tx, nqf, nqs, nqt, nfx, nsx, ntx):
        toQFF  = Implies(fx > UB, nqf == self.qOff)
        toQFO  = Implies(fx < LB, nqf == self.qOn)
        toQFS  = Implies(And(LB <= fx, fx <= UB), nqf == qf)
        toQSF  = Implies(sx > UB, nqs == self.qOff)
        toQSO  = Implies(sx < LB, nqs == self.qOn)
        toQSS  = Implies(And(LB <= sx, sx <= UB), nqs == qs)
        toQTF  = Implies(tx > UB, nqt == self.qOff)
        toQTO  = Implies(tx < LB, nqt == self.qOn)
        toQTS  = Implies(And(LB <= tx, tx <= UB), nqt == qt)
        return And(toQFF, toQFO, toQFS, toQSF, toQSO, toQSS, toQTF, toQTO, toQTS, nfx == fx, nsx == sx, ntx == tx)

if __name__ == '__main__':
    const = Thermostat().reach([Real("tau_%s"%i) for i in range(10)])
#    s = z3.Solver()
#    s.add(const[0].z3Obj())
#    print(s.to_smt2())
#    print(s.check())
 





