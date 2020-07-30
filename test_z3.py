from z3 import *

#print(z3.tactics())

#for name in z3.tactics():
#    t = z3.Tactic(name)
#print(name, t.help(), t.param_descrs())

x, y = Bools('x y')
x1, y1 = Reals('x1 y1')
g = Goal()
# g2 = z3.Goal()
#g.add(z3.Implies(z3.Or(x, y), x))
#g.add(z3.Implies(z3.RealVal(4) < x1, z3.RealVal(2) < x1))
g.add(Implies(And(Not(x), y), x))
#g2.add(z3.Implies(z3.Implies(x, y), x))



t1 = Tactic('qe-light')
t2 = Tactic('simplify')
t3 = Tactic('unit-subsume-simplify')
t4 = Tactic('ctx-solver-simplify')
t  = Then(t3, t2)
#tt = z3.Then(z3.Repeat(t2), t4)
print(t4(g))


#print(g)

xx = Int('xx')
pp3 = Bool('p3')
s = Solver()
s.set(unsat_core=True)
s.assert_and_track(xx > 0,  'p1')
s.assert_and_track(xx != 1, 'p2')
s.assert_and_track(xx < 0,  pp3)
print(s.check())
c = s.unsat_core()
print(c)

