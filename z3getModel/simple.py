from z3 import *
a = Bool('p')
b = Real('x')
s = Solver()
s.add(Or(b < 5, b > 10), Or(a, b**2 == 2), Not(a))
s.check()
m = s.model()
for d in m.decls():
    print("type of %s : %s" %(d.name(), type(d.name())))
    if not isinstance(m[d], z3.z3.BoolRef):
        print("reach")
        print(m[d].as_decimal(4))
    print("type of value" + str(type(m[d])))
    print("%s = %s" %(d.name(), m[d]))
print(s.model()[a])
print(s.model()[b])
