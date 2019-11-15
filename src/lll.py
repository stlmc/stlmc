from dreal import *

x = Variable("x")
y = Variable("y")
z = Variable("z")

l = []
l.append(x)
l.append(y)
l.append(z)

ctx = Context()
ctx.precision = 0.00000000001
ctx.SetLogic(Logic.QF_NRA)

ctx.DeclareVariable(x)
ctx.DeclareVariable(y)
#ctx.Assert(x == y + 5)
zzz = int(5)

ll = []
ipip = (x == y + zzz)
print(str(ipip))
print(type(ipip))
#ll.append(ipip)
ll.append(x == y + 5)
ll.append(y == 2)
#ctx.Assert(ll[0])
#ctx.Assert(ll[1])
ctx.Assert(And(*ll))
result0 = ctx.CheckSat()
print(result0)

'''
import unittest

class simplesival(unittest.TestCase):
    
    def test_sat(self):
        x = Variable("x")
        y = Variable("y")
        ctx = Context()
        ctx.SetLogic(Logic.QF_NRA)
        ctx.DeclareVariable(x, -10, 10)
        ctx.DeclareVariable(y, -10, 10)
        ctx.Assert(x == y + 5)
        ctx.Assert(y == 2)
        result = ctx.CheckSat()
        print(type(result))
        self.assertTrue(result)
        #assertEqual(result[y].mid(), 2)
        #assertEqual(result[x].mid(), 2 + 5)
        ctx.Exit()

    def test_unset(self):
        ctx = Context()
        ctx.SetLogic(Logic.QF_NRA)
        x = Variable("x")
        y = Variable("y")
        ctx.DeclareVariable(x, -10, 10)
        ctx.DeclareVariable(y, -10, 10)
        ctx.Assert(x == y + 5)
        ctx.Assert(y == x - 3)
        result = ctx.CheckSat()
        print(type(result))
        self.assertFalse(result)
        ctx.Exit()

#unittest.main()
#simplesival.test()
#simplesival.unsetTest()
if __name__ == '__main__':
    unittest.main()
'''
