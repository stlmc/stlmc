from z3 import *

class Thermostat:
    qOn  = BoolVal(True)
    qOff = BoolVal(False)

    def reach(self, ts):
        k   = len(ts) - 1
        q   = [Bool("m%s"%i)   for i in range(k+1)]
        x   = [Real("x%s"%i)   for i in range(k+1)]
        xt  = [Real("x%st"%i)   for i in range(k+1)] # at the end of mode

        prP = [Bool("p_%s"%i)  for i in range(k)] # p holds if x >= 20
        prQ = [Bool("q_%s"%i)  for i in range(k)] # q holds if mode On

        # reachability
        const = []
        const.append(self.init(q[0], x[0]))
        const.append(ts[0] >= 0)
        for i in range(k):
            const.append(self.flow(xt[i], q[i], x[i], ts[i+1] - ts[i]))
            const.append(self.jump(q[i], xt[i], q[i+1], x[i+1]))
            const.append(self.inv(q[i], x[i], ts[i+1] - ts[i]))
            const.append(ts[i] < ts[i+1])

        # STL props
        for i in range(k):
            pass
            const.append(self.propP(prP[i], q[i], x[i], ts[i+1] - ts[i]))
            const.append(self.propQ(prQ[i], q[i], x[i], ts[i+1] - ts[i]))
        return const


    def init(self, q0, v0):
        return And(q0 == self.qOff, v0 > 12, v0 < 14)

    def flow(self, nx, q, x, time):
        flowOn  = Implies(q == self.qOn,  nx == x + 0.3 * time)
        flowOff = Implies(q == self.qOff, nx == x - 0.2 * time)
        return And(flowOn, flowOff)

    def jump(self, q, x, nq, nx):
        toOn  = Implies(x < 16, nq == self.qOn)
        toOff = Implies(x > 24, nq == self.qOff)
        toQ   = Implies(And(16 <= x, x <= 24), nq == q)
        return And(toOn, toOff, toQ, nx == x)

    def inv(self, q, x, time):
        invOn  = Implies(q == self.qOn,  30 - x > 0.3 * time)
        invOff = Implies(q == self.qOff, x - 10 > 0.2 * time)
        return And(invOn, invOff)

    def propP(self, prp, q, x, time):
        c1 = Implies(And(prp, q == self.qOn),       x >= 20)
        c2 = Implies(And(prp, q == self.qOff),      And(x >= 20, x - 20 > 0.2 * time))
        c3 = Implies(And(Not(prp), q == self.qOn),  And(x < 20,  20 - x > 0.3 * time))
        c4 = Implies(And(Not(prp), q == self.qOff), x < 20)
        return And(c1, c2, c3, c4)

    def propQ(self, prq, q, x, time):
        return prq == q


if __name__ == '__main__':
    const = Thermostat().reach([Real("tau_%s"%i) for i in range(10)])
    s = Solver()
    s.add(const)
    print(s.to_smt2())
    print(s.check())
    print (s.model())

