from stlmcPy.constraints.constraints import Real, RealVal, Add, Ode, Lt, Sub, Gt, BoolVal
from stlmcPy.hybrid_automaton.hybrid_automaton import HybridAutomaton, merge, subsumption

ha1 = HybridAutomaton("ha1")
ha2 = HybridAutomaton("ha2")

var_vec = [Real("x"), Real("y"), Real("z")]
exps1 = [[RealVal("1"), Add(Real("y"), RealVal("2")), RealVal("4")],
         [RealVal("0"), RealVal("-1"), RealVal("1")],
         [RealVal("-1"), RealVal("-1"), RealVal("-1")]]

invs1 = [Lt(Real("x"), RealVal("3")),
         Lt(Real("y"), RealVal("3")),
         Lt(Real("z"), RealVal("3"))]

exps2 = [[RealVal("1"), Sub(Real("y"), RealVal("2")), RealVal("4")],
         [RealVal("11"), RealVal("10"), RealVal("9")],
         [RealVal("-1"), RealVal("-1"), RealVal("-1")]]

invs2 = [Lt(Real("x"), RealVal("3")),
         Lt(Real("y"), RealVal("100")),
         Lt(Real("z"), RealVal("5"))]

m1_list = list()
m2_list = list()

for i in range(3):
    m = ha1.new_mode("m1_{}".format(i))
    m.set_dynamics(Ode(var_vec, exps1[i]))
    m.set_invariant(invs1[i])
    m1_list.append(m)

m1_list.append(ha1.new_mode("error", is_error=True))

for i in range(3):
    m = ha2.new_mode("m2_{}".format(i))
    m.set_dynamics(Ode(var_vec, exps2[i]))
    m.set_invariant(invs2[i])
    m2_list.append(m)

m2_list.append(ha2.new_mode("error", is_error=True))

guard1 = [Lt(Real("x"), RealVal("3")),
          Lt(Real("x"), RealVal("3")),
          Lt(Real("x"), RealVal("3"))]

guard2 = [Lt(Real("x"), RealVal("3")),
          Lt(Real("x"), RealVal("3")),
          Lt(Real("x"), RealVal("3"))]

for i, m1 in enumerate(m1_list):
    if i < len(m1_list) - 1:
        trans = ha1.new_transition("trans{}".format(i), m1_list[i], m1_list[i + 1])
        trans.set_guard(guard1[i])

for i, m2 in enumerate(m2_list):
    if i < len(m2_list) - 1:
        trans = ha2.new_transition("trans{}".format(i), m2_list[i], m2_list[i + 1])
        trans.set_guard(guard2[i])

new_ha = merge(ha1, ha2)
print(ha1)
print(ha2)
print(new_ha)

# print(subsumption(None, None))

