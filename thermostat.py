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

        # reachability
        const = []
        const.append(self.init(qf[0], qs[0], qt[0], x1.start[0], x2.start[0], x3.start[0]))

        const.append(ts[0] <= RealVal(0))
        
        for i in range(k):
            const.append(self.jump(qf[i], qs[i], qt[i], x1.end[i], x2.end[i], x3.end[i], qf[i+1], qs[i+1], qt[i+1], x1.start[i+1], x2.start[i+1], x3.start[i+1]))

        variables = []
        for i in range(len(const)):
            variables += const[i].getVars()
        variables =removeDup(variables)
        return const 

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
    s = z3.Solver()
    s.add(const[0].z3Obj())
    print(s.to_smt2())
    print(s.check())
 





