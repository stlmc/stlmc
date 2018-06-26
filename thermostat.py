from interface import *

gT = RealVal(20)
LB = RealVal(16)
UB = RealVal(24)
MAX = RealVal(30)
MIN = RealVal(10)

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

        s   = [Real("s_%s"%i)   for i in range(3)] # the size of each room
        h   = [Real("h_%s"%i)   for i in range(3)] # heater's power of the each room
        d   = [Real("d_%s"%i)   for i in range(2)] # the size of the open door of the each room

        prPF = [Bool("pf_%s"%i)  for i in range(k)] # pf holds if fx <= 17
        prQF = [Bool("qf_%s"%i)  for i in range(k)] # qf holds if fx >= 20

        prPS = [Bool("ps_%s"%i)  for i in range(k)] # ps holds if sx <= 17
        prQS = [Bool("qs_%s"%i)  for i in range(k)] # qs holds if sx >= 20

        prPT = [Bool("pt_%s"%i)  for i in range(k)] # pt holds if tx <= 17
        prQT = [Bool("qt_%s"%i)  for i in range(k)] # qt holds if tx >= 20
        
        fxOff = -s[0] * (Real('const' + x1.id) - (d[0] * Real('const' + x2.id)))
        fxOn = s[0] * (h[0] -(Real('const' + x1.id) - (d[0] * Real('const' + x2.id))))
        sxOff = -s[1] * (Real('const' + x2.id) -(d[0] * Real('const' + x1.id) + d[1] * Real('const' + x3.id)))
        sxOn = s[1] * (h[1] - (Real('const' + x2.id) - (d[0] * Real('const' + x1.id) + d[1] * Real('const' + x3.id))))
        txOff = -s[2] * (Real('const' + x3.id) - (d[1] * Real('const' + x2.id)))
        txOn = s[2] * (h[2] - (Real('const' + x3.id) - (d[1] * Real('const' + x2.id))))

        flow_1 = {x1.id: fxOff, x2.id: sxOff, x3.id: txOff, ('const' + x1.id): 0, ('const' + x2.id): 0, ('const' + x3.id): 0}
        flow_2 = {x1.id: fxOff, x2.id: sxOff, x3.id: txOn, ('const' + x1.id): 0, ('const' + x2.id): 0, ('const' + x3.id): 0}
        flow_3 = {x1.id: fxOff, x2.id: sxOn, x3.id: txOff, ('const' + x1.id): 0, ('const' + x2.id): 0, ('const' + x3.id): 0}
        flow_4 = {x1.id: fxOff, x2.id: sxOn, x3.id: txOn, ('const' + x1.id): 0, ('const' + x2.id): 0, ('const' + x3.id): 0}
        flow_5 = {x1.id: fxOn, x2.id: sxOff, x3.id: txOff, ('const' + x1.id): 0, ('const' + x2.id): 0, ('const' + x3.id): 0}
        flow_6 = {x1.id: fxOn, x2.id: sxOff, x3.id: txOn, ('const' + x1.id): 0, ('const' + x2.id): 0, ('const' + x3.id): 0}
        flow_7 = {x1.id: fxOn, x2.id: sxOn, x3.id: txOff, ('const' + x1.id): 0, ('const' + x2.id): 0, ('const' + x3.id): 0}
        flow_8 = {x1.id: fxOn, x2.id: sxOn, x3.id: txOn, ('const' + x1.id): 0, ('const' + x2.id): 0, ('const' + x3.id): 0}
 
        defineODE = [flow_1, flow_2, flow_3, flow_4, flow_5, flow_6, flow_7, flow_8]

        # reachability
        const = []
        const.append(self.init(qf[0], qs[0], qt[0], x1.start[0], x2.start[0], x3.start[0]))

        const.append(ts[0] <= RealVal(0))
        
        for i in range(k):
            const.append(self.flow(qf[i], qs[i], qt[i], x1, x2, x3, ts[i+1] - ts[i], defineODE, i))
            const.append(self.jump(qf[i], qs[i], qt[i], x1.end[i], x2.end[i], x3.end[i], qf[i+1], qs[i+1], qt[i+1], x1.start[i+1], x2.start[i+1], x3.start[i+1]))
            const.append(self.inv(qf[i], qs[i], qt[i], x1, x2, x3, ts[i+1] - ts[i], i))

        variables = []
        for i in range(len(const)):
            variables += const[i].getVars()
        variables =removeDup(variables)

        return const 

    def inv(self, qf, qs, qt, s1, s2, s3, time, k):
        invFFF  = Implies(And(qf == self.qOff, qs == self.qOff, qt == self.qOff), Forall(1, time, And(s1.end[k] > RealVal(10), s2.end[k] > RealVal(10), s3.end[k] > RealVal(10)))) 
        invFFO  = Implies(And(qf == self.qOff, qs == self.qOff, qt == self.qOn), Forall(2, time, And(s1.end[k] > RealVal(10), s2.end[k] > RealVal(10), s3.end[k] < RealVal(30))))
        invFOF  = Implies(And(qf == self.qOff, qs == self.qOn, qt == self.qOff), Forall(3, time, And(s1.end[k] > RealVal(10), s2.end[k] < RealVal(30), s3.end[k] > RealVal(30))))
        invFOO  = Implies(And(qf == self.qOff, qs == self.qOn, qt == self.qOn), Forall(4, time, And(s1.end[k] > RealVal(10), s2.end[k] < RealVal(30), s3.end[k] < RealVal(30))))
        invOFF  = Implies(And(qf == self.qOn, qs == self.qOff, qt == self.qOff), Forall(5, time, And(s1.end[k] < RealVal(30), s2.end[k] > RealVal(10), s3.end[k] > RealVal(10))))
        invOFO  = Implies(And(qf == self.qOn, qs == self.qOff, qt == self.qOn), Forall(6, time, And(s1.end[k] < RealVal(30), s2.end[k] > RealVal(10), s3.end[k] < RealVal(30))))
        invOOF  = Implies(And(qf == self.qOn, qs == self.qOn, qt == self.qOff), Forall(7, time, And(s1.end[k] < RealVal(30), s2.end[k] < RealVal(30), s3.end[k] > RealVal(10))))
        invOOO  = Implies(And(qf == self.qOn, qs == self.qOn, qt == self.qOn), Forall(8, time, And(s1.end[k] < RealVal(30), s2.end[k] < RealVal(30), s3.end[k] < RealVal(30))))
        return And(invFFF, invFFO, invFOF, invFOO, invOFF, invOFO, invOOF, invOOO)

    def flow(self, qf, qs, qt, s1, s2, s3, time, ODElist, k):
        toFFF  = Implies(And(qf == self.qOff, qs == self.qOff, qt == self.qOff), Integral([s1.end[k], s2.end[k], s3.end[k]], [s1.start[k], s2.start[k], s3.start[k]], time, ODElist[0], 1, [s1.id, s2.id, s3.id], k))
        toFFO  = Implies(And(qf == self.qOff, qs == self.qOff, qt == self.qOn), Integral([s1.end[k], s2.end[k], s3.end[k]], [s1.start[k], s2.start[k], s3.start[k]], time, ODElist[1], 2, [s1.id, s2.id, s3.id], k))
        toFOF  = Implies(And(qf == self.qOff, qs == self.qOn, qt == self.qOff), Integral([s1.end[k], s2.end[k], s3.end[k]], [s1.start[k], s2.start[k], s3.start[k]], time, ODElist[2], 3, [s1.id, s2.id, s3.id], k))
        toFOO  = Implies(And(qf == self.qOff, qs == self.qOn, qt == self.qOn), Integral([s1.end[k], s2.end[k], s3.end[k]], [s1.start[k], s2.start[k], s3.start[k]], time, ODElist[3], 4, [s1.id, s2.id, s3.id], k))
        toOFF  = Implies(And(qf == self.qOn, qs == self.qOff, qt == self.qOff), Integral([s1.end[k], s2.end[k], s3.end[k]], [s1.start[k], s2.start[k], s3.start[k]], time, ODElist[4], 5, [s1.id, s2.id, s3.id], k))
        toOFO  = Implies(And(qf == self.qOn, qs == self.qOff, qt == self.qOn), Integral([s1.end[k], s2.end[k], s3.end[k]], [s1.start[k], s2.start[k], s3.start[k]], time, ODElist[5], 6, [s1.id, s2.id, s3.id], k))
        toOOF  = Implies(And(qf == self.qOn, qs == self.qOn, qt == self.qOff), Integral([s1.end[k], s2.end[k], s3.end[k]], [s1.start[k], s2.start[k], s3.start[k]], time, ODElist[6], 7, [s1.id, s2.id, s3.id], k))
        toOOO  = Implies(And(qf == self.qOn, qs == self.qOn, qt == self.qOn), Integral([s1.end[k], s2.end[k], s3.end[k]], [s1.start[k], s2.start[k], s3.start[k]], time, ODElist[7], 8, [s1.id, s2.id, s3.id], k))
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
 





