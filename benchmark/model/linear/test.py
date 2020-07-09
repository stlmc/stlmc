import z3
x = z3.Real('x')
y = z3.Real('y')
print(z3.simplify(z3.Implies(z3.And(z3.Not(x >= 0), y < 0), z3.And(x >= 0, y < 0))))


print(z3.simplify(z3.Implies(z3.And(x >= 0, y < 0), z3.And(y < 0, x >= 0))))
print(z3.simplify(z3.Implies(z3.And(x >= 0, y < 0), z3.And(x >= 0, y < 0))))

#print(z3.simplify(z3.Implies(z3.And(x >= 0, y < 0), z3.And(x >= 0, y < 0))))
#print(z3.simplify(z3.Implies(z3.And(z3.Not(x >= 0), y < 0), z3.And(x >= 0, y < 0))))
