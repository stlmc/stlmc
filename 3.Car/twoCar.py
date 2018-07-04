from core.interface import *
from core.dRealHandler import *
import os, sys
from model import *
import math 

L1 = RealVal(1)
L2 = RealVal(1.5)
V1Acc = RealVal(4.0)
V1Dec = RealVal(0.3)
V2Acc = RealVal(3.0)
V2Dec = RealVal(0.5)
Keep = RealVal(1)
#Acc: 1, Keep: 0, Dec: -1

class Car(Model):
    mx1 = Real('mx1')
    mx2 = Real('mx2')
    x1 = Real('x1')
    x2 = Real('x2')
    mx1Next = NextVar(mx1)
    mx2Next = NextVar(mx2)
    x1Next = NextVar(x1)
    x2Next = NextVar(x2)
    proPF = Bool('pf')
    proQF = Bool('qf')

    def __init__(self):
        mode = [self.mx1, self.mx2]
        vars = {self.x1: (0, 100), self.x2: (0, 100)}
        init = And(And(self.mx1 == RealVal(1), self.mx2 == RealVal(1)), self.x1 == RealVal(0), self.x2 == RealVal(3))


        flow = {And(self.mx1 == RealVal(1), self.mx2 == RealVal(1)): {self.x1: V1Acc, self.x2: V2Acc}, \
               And(self.mx1 == RealVal(1), self.mx2 == RealVal(0)): {self.x1: V1Acc, self.x2: Keep}, \
               And(self.mx1 == RealVal(1), self.mx2 == -RealVal(1)): {self.x1: V1Acc, self.x2: V2Dec}, \
               And(self.mx1 == RealVal(0), self.mx2 == RealVal(1)): {self.x1: Keep, self.x2: V2Acc}, \
               And(self.mx1 == RealVal(0), self.mx2 == RealVal(0)): {self.x1: Keep, self.x2: Keep}, \
               And(self.mx1 == RealVal(0), self.mx2 == -RealVal(1)): {self.x1: Keep, self.x2: V2Dec}, \
               And(self.mx1 == -RealVal(1), self.mx2 == RealVal(1)): {self.x1: V1Dec, self.x2: V2Acc}, \
               And(self.mx1 == -RealVal(1), self.mx2 == RealVal(0)): {self.x1: V1Dec, self.x2: Keep}, \
               And(self.mx1 == -RealVal(1), self.mx2 == -RealVal(1)): {self.x1: V1Dec, self.x2: V2Dec}}
  
        inv = {And(self.mx1 == RealVal(1), self.mx2 == RealVal(1)): self.x2 >= self.x1, \
               And(self.mx1 == RealVal(1), self.mx2 == RealVal(0)): self.x2 >= self.x1, \
               And(self.mx1 == RealVal(1), self.mx2 == -RealVal(1)): self.x2 >= self.x1, \
               And(self.mx1 == RealVal(0), self.mx2 == RealVal(1)): self.x2 >= self.x1, \
               And(self.mx1 == RealVal(0), self.mx2 == RealVal(0)): self.x2 >= self.x1, \
               And(self.mx1 == RealVal(0), self.mx2 == -RealVal(1)): self.x2 >= self.x1, \
               And(self.mx1 == -RealVal(1), self.mx2 == RealVal(1)): self.x2 >= self.x1, \
               And(self.mx1 == -RealVal(1), self.mx2 == RealVal(0)): self.x2 >= self.x1, \
               And(self.mx1 == -RealVal(1), self.mx2 == -RealVal(1)): self.x2 >= self.x1}


        jump = {self.x2 - self.x1 <  RealVal(1): And(And(self.mx1Next == -RealVal(1), self.mx2Next == RealVal(1)), self.x1Next == self.x1, self.x2Next == self.x2), \
               And((self.x2 - self.x1) >= RealVal(1), (self.x2 - self.x1) < RealVal(2)): And(And(self.mx1Next == RealVal(0), self.mx2Next == RealVal(1)), self.x1Next == self.x1, self.x2Next == self.x2), \
               And((self.x2 - self.x1) >= RealVal(2), (self.x2 - self.x1) < RealVal(3)): And(And(self.mx1Next == RealVal(1), self.mx2Next == RealVal(1)), self.x1Next == self.x1, self.x2Next == self.x2), \
               And((self.x2 - self.x1) >= RealVal(3), (self.x2 - self.x1) < RealVal(4)): And(And(self.mx1Next == RealVal(1), self.mx2Next == RealVal(0)), self.x1Next == self.x1, self.x2Next == self.x2), \
               And((self.x2 - self.x1) >= RealVal(4), (self.x2 - self.x1) < RealVal(5)): And(And(self.mx1Next == RealVal(0), self.mx2Next == -RealVal(1)), self.x1Next == self.x1, self.x2Next == self.x2), \
               self.x2 - self.x1 >= RealVal(5): And(And(self.mx1Next == RealVal(1)), self.mx2Next == -RealVal(1), self.x1Next == self.x1, self.x2Next == self.x2)}

        prop = {self.proPF : And(self.mx1 == RealVal(0), self.mx2 == RealVal(0)), self.proQF: self.x2 - self.x1 < RealVal(9) }

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Car()
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












