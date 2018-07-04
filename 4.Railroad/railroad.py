import os, sys, io
#sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.interface import *
from core.dRealHandler import *
from model import *

FAR = RealVal(1)
APPROACH = RealVal(2)
NEAR = RealVal(3)
PAST = RealVal(4)

Vfar = RealVal(10)
Vapproach = RealVal(5)
Vnear = RealVal(1)

#Far: 1, approach: 2, Near: 3, Past: 4

class Railroad(Model):
    tm = Real('tm')
    tx = Real('tx')
    tmNext = NextVar(tm)
    txNext = NextVar(tx)
    proPF = Bool('pf')
    proQF = Bool('qf')

    def __init__(self):
        mode = [self.tm]
        vars = {self.tx: (-20, 100)}
        init = And(self.tm == FAR, self.tx >= RealVal(5), self.tx <= RealVal(8)}

        flow = {self.tm == FAR: {self.fx: Vfar}, \
                self.tm == APPROACH: {self.fx: Vapproach}, \
                self.tm == NEAR: {self.fx: Vnear}, \
                self.tm == PAST: {self.fx: Vfar}}

        inv = {self.tm == FAR: And(self.tx >= RealVal(40), self.tx <= RealVal(95)), \
               self.tm == APPROACH: And(self.tx < RealVal(40), self.tx >= RealVal(20)), \
                self.tm == NEAR: And(self.tx < RealVal(20), self.tx >= RealVal(5)), \
                self.tm == PAST: And(self.tx < RealVal(5), self.tx >= -RealVal(10))} 
              
        jump = {And(self.tx < RealVal(40), self.tx >= RealVal(20)): And(self.tmNext == APPROACH, self.txNext == self.tx), \
                And(self.tx < RealVal(20), self.tx >= RealVal(5): And(self.tmNext == NEAR, self.txNext == self.tx), \
                And(self.tx < RealVal(5), self.tx >= -RealVal(10)): And(self.tmNext == PAST, self.txNext == RealVal(95)), \
                And(self.tx >= RealVal(40), self.tx <= RealVal(95): And(self.tmNext == FAR, self.txNext == self.tx)} 

        prop = {}

        super().__init__(mode, vars, init, flow, inv, jump, prop)


if __name__ == '__main__':
    model = Railroad()
    const = model.reach(2)

    output = io.StringIO()
    printObject = dRealHandler(const, output, model.variables, model.flowDict)
    printObject.callAll()
    f = open('test.smt2', 'w')
    f.write(output.getvalue())
    f.close()

    s = z3.Solver()
    for i in range(len(const)):
        s.add(const[i].z3Obj())
#    print(s.to_smt2())
    print(s.check())

