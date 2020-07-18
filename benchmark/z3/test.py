from z3 import *

x = Real('x')
y = Real('y')
a = Bool('a')
s = Solver()
soft_constraints = [Not(a), Or(x + y > 0, y < 0), Or(y >= 0, x >= 0)]

for sc in soft_constraints:
    s.add(sc)
    '''
    if len(sc.children()) > 1:
        print(sc.children())
    if isinstance(sc, z3.And):
        print("and")
    if isinstance(sc, z3.Or):
        print("Or")
    '''
    # print(sc.children())

s.check()
el = list()
model = s.model()
print(model.eval(Or(x + y > 0, y < 0)))

'''
for mi in s.objects():
    el.append(mi == objects[mi])
    print(type(mi))
    if not (str(objects[mi]) == "False"):
        print(type(float(str(objects[mi]))))

print(type(0.4))
print(type(x))

for sc in soft_constraints:
    ms = Solver()
    ms.add(sc)
    print(ms.check([mi == objects[mi] for mi in s.objects()]))
    #nm = ms.objects()
    #print(nm.eval(x))

'''


