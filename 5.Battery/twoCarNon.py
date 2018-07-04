from core.interface import *
from core.dRealHandler import *
import os, sys
from model import *
import math 

K = RealVal(0.122)
C = RealVal(0.166)

#On: 1, Off: 0, Dead: -1

class Battery(Model):
    mb1 = Real('mb1')
    mb2 = Real('mb2')
    d1 = Real('d1')
    d2 = Real('d2')
    g1 = Real('g1')
    g2 = Real('g2')
    constd1 = Real('constd1')
    constd2 = Real('constd2')
    mb1Next = NextVar(mb1)
    mb2Next = NextVar(mb2)
    d1Next = NextVar(d1)
    d2Next = NextVar(d2)
    g1Next = NextVar(g1)
    g2Next = NextVar(g2)
    constd1Next = NextVar(constd1)
    constd2Next = NextVar(constd2)
    proPF = Bool('pf')
    proQF = Bool('qf')

    def __init__(self):
        mode = [self.mb1, self.mb2]
        vars = {self.d1: (-10, 10), self.d2: (-10, 10), self.g1: (-10, 10), self.g2: (-10, 10), self.constd1: (-10, 10), self.constd2: (-10, 10)}
        init = And(And(self.mb1 == RealVal(1), self.mb2 == RealVal(1)), self.g1 == RealVal(8.5), self.d1 == RealVal(0), self.g2 == RealVal(7.5), self.d2 == RealVal(0), And(self.constd1 == self.d1, self.constd2 == self.d2))

        flow = {And(self.mb1 == RealVal(1), self.mb2 == RealVal(1)): {self.d1: (RealVal(0.5) / C) - (K * self.d1), self.d2: (RealVal(0.5) / C) - (K * self.d2), self.g1: -RealVal(0.5), self.g2: -RealVal(0.5), self.constd1: RealVal(0), self.constd2: RealVal(0)}, \
               And(self.mb1 == RealVal(1), self.mb2 == RealVal(0)): {self.d1: (RealVal(1) / C) - (K * self.d1), self.d2: -(K * self.d2), self.g1: -RealVal(1), self.g2: RealVal(0), self.constd1: RealVal(0), self.constd2: RealVal(0)}, \
               And(self.mb1 == RealVal(0), self.mb2 == RealVal(1)): {self.d1: -(K * self.d1), self.d2: (RealVal(1) / C) - (K * self.d2), self.g1: RealVal(0), self.g2: -RealVal(1), self.constd1: RealVal(0), self.constd2: RealVal(0)}, \
               And(self.mb1 == -RealVal(1), self.mb2 == RealVal(1)): {self.d1: RealVal(0), self.d2: (RealVal(1) / C) - (K * self.d2), self.g1: RealVal(0), self.g2: -RealVal(1), self.constd1: RealVal(0), self.constd2: RealVal(0)}, \
               And(self.mb1 == RealVal(1), self.mb2 == -RealVal(1)): {self.d1: (RealVal(1) / C) - (K * self.d1), self.d2: RealVal(0), self.g1: -RealVal(1), self.g2: RealVal(0), self.constd1: RealVal(0), self.constd2: RealVal(0)}, \
               And(self.mb1 == -RealVal(1), self.mb2 == -RealVal(1)): {self.d1: RealVal(0), self.d2: RealVal(0), self.g1: RealVal(0), self.g2: RealVal(0), self.constd1: RealVal(0), self.constd2: RealVal(0)}}
  
        inv = {}

        jump = {And(self.g1 > (RealVal(1) - C) * self.d1, self.g2 > (RealVal(1) - C) * self.d2): And(And(self.mb1Next == RealVal(1), self.mb2Next == RealVal(1)), self.d1Next == self.d1, self.g1Next == self.g1, self.d2Next == self.d2, self.g2Next == self.g2, self.constd1Next == self.d1, self.constd2Next == self.d2), \
               And(self.g1 > (RealVal(1) - C) * self.d1, self.g2 > (RealVal(1) - C) * self.d2): And(And(self.mb1Next == RealVal(1), self.mb2Next == RealVal(0)), self.d1Next == self.d1, self.g1Next == self.g1, self.d2Next == self.d2, self.g2Next == self.g2, self.constd1Next == self.d1, self.constd2Next == self.d2), \
               And(self.g1 > (RealVal(1) - C) * self.d1, self.g2 > (RealVal(1) - C) * self.d2): And(And(self.mb1Next == RealVal(0), self.mb2Next == RealVal(1)), self.d1Next == self.d1, self.g1Next == self.g1, self.d2Next == self.d2, self.g2Next == self.g2, self.constd1Next == self.d1, self.constd2Next == self.d2), \
               And(self.g1 <= (RealVal(1) - C) * self.d1, self.g2 > (RealVal(1) - C) * self.d2): And(And(self.mb1Next == -RealVal(1), self.mb2Next == RealVal(1)), self.d1Next == self.d1, self.g1Next == self.g1, self.d2Next == self.d2, self.g2Next == self.g2, self.constd1Next == self.d1, self.constd2Next == self.d2), \
               And(self.g1 > (RealVal(1) - C) * self.d1, self.g2 <= (RealVal(1) - C) * self.d2): And(And(self.mb1Next == RealVal(1), self.mb2Next == -RealVal(1)), self.d1Next == self.d1, self.g1Next == self.g1, self.d2Next == self.d2, self.g2Next == self.g2, self.constd1Next == self.d1, self.constd2Next == self.d2), \
               And(self.g1 <= (RealVal(1) - C) * self.d1, self.g2 <= (RealVal(1) - C) * self.d2): And(And(self.mb1Next == -RealVal(1), self.mb2Next == -RealVal(1)), self.d1Next == self.d1, self.g1Next == self.g1, self.d2Next == self.d2, self.g2Next == self.g2, self.constd1Next == self.d1, self.constd2Next == self.d2)}

        prop = {}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Battery()
    const = model.reach(4)

    output = io.StringIO()
    printObject = dRealHandler(const, output, model.variables, model.flowDict)
    printObject.callAll()
#    print (output.getvalue())
    dRealname=os.path.basename(os.path.realpath(sys.argv[0]))
    dRealname = dRealname[:-3]
    dRealname += '.smt2'
    f = open(dRealname, 'w')
    f.write(output.getvalue())
    f.close()
    try:
        s = z3.Solver()
        for i in range(len(const)):
            s.add(const[i].z3Obj())
#        print(s.to_smt2())
        print(s.check())
    except z3constODEerror:
        print("receive nonlinear ODE")












