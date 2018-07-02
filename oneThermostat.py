from core.interface import *
import os, sys

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
    qOn  = BoolVal(True)
    qOff = BoolVal(False)

    def reach(self, ts, filename):
        k   = len(ts) - 1
        q   = [Bool("m%s"%i)   for i in range(k+1)]

        x1 = stateDeclare('fx', k)
        constx1 = stateDeclare('constfx', k)

        prP = [Bool("p_%s"%i)  for i in range(k)] # p holds if x >= 20
        prQ = [Bool("q_%s"%i)  for i in range(k)] # q holds if mode On


        fxOff = -S1 * (Real(constx1.id))
        fxOn = S1 * (H1 -(Real(constx1.id)))

        flow_1 = {x1.id: fxOff, constx1.id: RealVal(0)}
        flow_2 = {x1.id: fxOn, constx1.id: RealVal(0)}

        varRange = {x1.id: (-20, 100), constx1.id: (-20, 100)}

        ODE_1 = ODE(1, flow_1)
        ODE_2 = ODE(2, flow_2)

        defineODE = [ODE_1, ODE_2]

        # reachability
        const = []
        const.append(self.init(q[0], x1.start[0], constx1.start[0]))
        const.append(ts[0] >= RealVal(0))

        for i in range(k):
            const.append(Real('time' + str(i)) == (ts[i+1] - ts[i]))
            const.append(self.flow(q[i], [x1.start[i], constx1.start[i]], [x1.end[i], constx1.end[i]], Real('time' + str(i)), defineODE))
            const.append(self.jump(q[i], x1.end[i], q[i+1], x1.start[i+1], constx1.start[i+1]))
            const.append(self.inv(q[i], [x1.id], [x1.start[i]], [x1.end[i]], Real('time' + str(i))))
            const.append(ts[i] < ts[i+1])
            const.append(And(constx1.start[i] == constx1.end[i]))

        # STL props
        for i in range(k):
            const.append(self.propP(prP[i], q[i], [x1.id], [x1.start[i]], [x1.end[i]], Real('time' + str(i))))
            const.append(self.propQ(prQ[i], q[i], [x1.id], [x1.start[i]], [x1.end[i]], Real('time' + str(i))))


        printObject = printHandler(const, filename, varRange, defineODE)

        return (const, printObject)



    def init(self, qf, fv0, conx1): 
        return And(qf == self.qOff, fv0 >= gT - RealVal(1), fv0 <= gT + RealVal(1), conx1 == fv0)

    def flow(self, qf, start, end, time, ODElist):
        flowOff  = Implies(qf == self.qOff, Integral(end, start, time, ODElist[0])) 
        flowOn = Implies(qf == self.qOn, Integral(end, start, time, ODElist[1]))
        return And(flowOn, flowOff)

    def jump(self, qf, fx, nqf, nfx, conx1): 
        toOn  = Implies(fx < LB, nqf == self.qOn) 
        toOff = Implies(fx > UB, nqf == self.qOff) 
        toQ   = Implies(And(LB <= fx, fx <= UB), nqf == qf) 
        return And(conx1 == fx, toOn, toOff, toQ, nfx == fx)

    def inv(self, qf, variables, start, end, time):
        startDict = {}
        endDict = {}
        for i in range(len(variables)):
            startDict[variables[i]] = start[i]
            endDict[variables[i]] = end[i]
        x1var = Real(variables[0]) 
        invOn  = Implies(qf == self.qOn,  Forall(1, time, x1var < RealVal(30), startDict, endDict))
        invOff = Implies(qf == self.qOff, Forall(1, time, x1var > RealVal(10), startDict, endDict))
        return And(invOn, invOff)

    def propP(self, prp, qf, variables, start, end, time):
        startDict = {}
        endDict = {}
        for i in range(len(variables)):
            startDict[variables[i]] = start[i]
            endDict[variables[i]] = end[i]
        x1var = Real(variables[0])
        c1 = Implies(And(prp, qf == self.qOn),  Forall(1, time, x1var >= RealVal(20), startDict, endDict))
        c2 = Implies(And(prp, qf == self.qOff),     Forall(2, time, x1var > RealVal(20), startDict, endDict)) 
        c3 = Implies(And(Not(prp), qf == self.qOn),  Forall(1, time, x1var < RealVal(20), startDict, endDict))
        c4 = Implies(And(Not(prp), qf == self.qOff), Forall(2, time, x1var < RealVal(20), startDict, endDict))
        return And(c1, c2, c3, c4)

    def propQ(self, prq, qf, variables, start, end, time):
        return prq == qf


if __name__ == '__main__':
    filename=os.path.basename(os.path.realpath(sys.argv[0]))
    filename = filename[:-2]
    filename += 'smt2'
    const = Thermostat().reach([Real("tau_%s"%i) for i in range(15)], filename)[0]
    s = z3.Solver()
    for i in range(len(const)):
        s.add(const[i].z3Obj())
#    print(s.to_smt2())
#    print(s.check())





