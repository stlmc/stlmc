from dreal import *

ctx = Context()
#vars = Variables([x])
x = Variable("t")
ctx.DeclareVariable(x)
pred = [x < 7, x > 0, forall([x], sin(x) > -0.9)]
f_sat = And(*pred)
ctx.Assert(f_sat)
result = ctx.CheckSat()

#result = CheckSatisfiability(f_sat, 0.001)
print(result)
