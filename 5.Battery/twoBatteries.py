import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.interface import *
from core.dRealHandler import *
from model import *

K = RealVal(0.122)
C = RealVal(0.166)

#On: 1, Off: 0, Dead: -1

class Battery(Model):
    def __init__(self):
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

        mode = [mb1, mb2]
        vars = {d1: (-10, 10), d2: (-10, 10), g1: (-10, 10), g2: (-10, 10), constd1: (-10, 10), constd2: (-10, 10)}
        init = And(And(mb1 == RealVal(1), mb2 == RealVal(1)), g1 == RealVal(8.5), d1 == RealVal(0), g2 == RealVal(7.5), d2 == RealVal(0), And(constd1 == d1, constd2 == d2))

        flow = {And(mb1 == RealVal(1), mb2 == RealVal(1)): {d1: (RealVal(0.5) / C) - (K * constd1), d2: (RealVal(0.5) / C) - (K * constd2), g1: -RealVal(0.5), g2: -RealVal(0.5), constd1: RealVal(0), constd2: RealVal(0)}, \
               And(mb1 == RealVal(1), mb2 == RealVal(0)): {d1: (RealVal(1) / C) - (K * constd1), d2: -(K * constd2), g1: -RealVal(1), g2: RealVal(0), constd1: RealVal(0), constd2: RealVal(0)}, \
               And(mb1 == RealVal(0), mb2 == RealVal(1)): {d1: -(K * constd1), d2: (RealVal(1) / C) - (K * constd2), g1: RealVal(0), g2: -RealVal(1), constd1: RealVal(0), constd2: RealVal(0)}, \
               And(mb1 == -RealVal(1), mb2 == RealVal(1)): {d1: RealVal(0), d2: (RealVal(1) / C) - (K * constd2), g1: RealVal(0), g2: -RealVal(1), constd1: RealVal(0), constd2: RealVal(0)}, \
               And(mb1 == RealVal(1), mb2 == -RealVal(1)): {d1: (RealVal(1) / C) - (K * constd1), d2: RealVal(0), g1: -RealVal(1), g2: RealVal(0), constd1: RealVal(0), constd2: RealVal(0)}, \
               And(mb1 == -RealVal(1), mb2 == -RealVal(1)): {d1: RealVal(0), d2: RealVal(0), g1: RealVal(0), g2: RealVal(0), constd1: RealVal(0), constd2: RealVal(0)}}
  
        inv = {And(mb1 == -RealVal(1), mb2 == -RealVal(1)): And(mb1Next == -RealVal(1), mb2Next == -RealVal(1))}

        jump = {And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(And(mb1Next == RealVal(1), mb2Next == RealVal(1)), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
               And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(And(mb1Next == RealVal(1), mb2Next == RealVal(0)), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
               And(g1 > (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(And(mb1Next == RealVal(0), mb2Next == RealVal(1)), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
               And(g1 <= (RealVal(1) - C) * d1, g2 > (RealVal(1) - C) * d2): And(And(mb1Next == -RealVal(1), mb2Next == RealVal(1)), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
               And(g1 > (RealVal(1) - C) * d1, g2 <= (RealVal(1) - C) * d2): And(And(mb1Next == RealVal(1), mb2Next == -RealVal(1)), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2), \
               And(g1 <= (RealVal(1) - C) * d1, g2 <= (RealVal(1) - C) * d2): And(And(mb1Next == -RealVal(1), mb2Next == -RealVal(1)), d1Next == d1, g1Next == g1, d2Next == d2, g2Next == g2, constd1Next == d1, constd2Next == d2)}

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












