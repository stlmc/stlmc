import z3

#print(z3.tactics())

#for name in z3.tactics():
#    t = z3.Tactic(name)
#print(name, t.help(), t.param_descrs())

x, y = z3.Bools('x y')
x1, y1 = z3.Reals('x1 y1')
g = z3.Goal()
# g2 = z3.Goal()
#g.add(z3.Implies(z3.Or(x, y), x))
#g.add(z3.Implies(z3.RealVal(4) < x1, z3.RealVal(2) < x1))
g.add(z3.Implies(z3.And(z3.Not(x), y), x))
#g2.add(z3.Implies(z3.Implies(x, y), x))



t1 = z3.Tactic('qe-light')
t2 = z3.Tactic('simplify')
t3 = z3.Tactic('unit-subsume-simplify')
t4 = z3.Tactic('ctx-solver-simplify')
t  = z3.Then(t3, t2)
#tt = z3.Then(z3.Repeat(t2), t4)
print(t4(g))


#print(g)



