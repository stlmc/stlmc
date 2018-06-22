from error import *
from mode import *
from typeEnum import *

class Node:
    def __init__(self, nodeType, nodeVars):
        self.nodeVars = []
        self.nodeType = nodeType
        self.nodeVars += nodeVars
    def __sub__(self, num):
        return Minus(self, num)
    def __add__(self, num):
        return Plus(self, num)
    def __mul__(self, num):
        return Mul(self, num)
    def __truediv__(self, num):
        return Div(self, num)
    def __eq__(self, num):
        if num.getType() == Type.BOOL:
            return Beq(self, num)
        else:
            return Numeq(self, num)
    def __lt__(self, num):
        return Lt(self, num)
    def __le__(self, num):
        return Le(self, num)
    def __gt__(self, num):
        return Gt(self, num)
    def __ge__(self, num):
        return Ge(self, num)
    def __neg__(self):
        return Neg(self)
    def getType(self):
        return self.nodeType
    def getVars(self):
        return self.nodeVars

class Leaf(Node):
    def size(self):
        return 0

class Constant(Leaf):
    def __init__(self, constType, value):
        super().__init__(constType, [])
        self.value = value
    def __repr__(self):
        return str(self.value)

class BoolVal(Constant):
    def __init__(self, value):
        if not(isinstance(value, bool)):
           raise TypeError()
        self.value = 'true' if value == True else 'false'
        super().__init__(Type.BOOL, self.value)

class RealVal(Constant):
    def __init__(self, value):
        super().__init__(Type.REAL, value)

class IntVal(Constant):
    def __init__(self, value):
        super().__init__(Type.INT, value)


class Variable(Leaf):
    def __init__(self, varType, var):
        super().__init__(varType, [var])
        self.var = var
    def __repr__(self):
        return str(self.var)

class Bool(Variable):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.BOOL, self)
    def __repr__(self):
        return str(self.id)

class Real(Variable):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.REAL, self)
    def __repr__(self):
        return str(self.id)

class Int(Variable):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.INT, self)
    def __repr__(self):
        return str(self.id)

class nonLeaf(Node):
    def __init__(self, op, nonLeafType, args):
        self.op = op
        self.children = []
        self.children += args
        variables = []
        for i in range(len(args)):
            variables += args[i].getVars()
        super().__init__(nonLeafType, variables)
    def size(self):
        size = 1
        for i in range(len(self.children)):
            size += self.children[i].size()
        return size
    def __repr__(self):
        result = '(' + self.op + ' '
        for i in range(len(self.children)):
            result += str(self.children[i])
            if i != len(self.children)-1:
                result += ' '
        result += ')'
        return result
 
class Relational(nonLeaf):
    def __init__(self, op, left, right):
        if not(left.getType() == right.getType() == Type.INT or left.getType() == right.getType() == Type.REAL):
            raise TypeError()
        self.left = left
        self.right = right
        super().__init__(op, Type.BOOL, [left, right]) 
    def getVars(self):
        return self.left.getVars() + self.right.getVars()

class Ge(Relational):
    def __init__(self, left, right):
        super().__init__('>=', left, right)

class Gt(Relational):
    def __init__(self, left, right):
        super().__init__('>', left, right)

class Le(Relational):
    def __init__(self, left, right):
        super().__init__('<=', left, right)

class Lt(Relational):
    def __init__(self, left, right):
        super().__init__('<', left, right)

class Numeq(Relational):
    def __init__(self, left, right):
        super().__init__('=', left, right)

class BinaryArithmetic(nonLeaf):
    def __init__(self, op, left, right):
        if not(left.getType() == right.getType() == Type.INT or left.getType() == right.getType() == Type.REAL):
            raise TypeError()
        self.left = left
        self.right = right
        super().__init__(op, left.getType(), [left, right])
    def getVars(self):
        return self.left.getVars() + self.right.getVars()

class Plus(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('+', left, right)

class Minus(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('-', left, right)

class Mul(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('*', left, right)

class Div(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('/', left, right)

class UnaryArithmetic(nonLeaf):
    def __init__(self, op, num):
        if not(num.getType() == Type.INT or num.getType() == Type.REAL):
            raise TypeError()
        self.num = num
        if num.getType() == Type.INT:
            result = [InTVal(0), num]
        else:
            result = [RealVal(0), num]
        super().__init__(op, num.getType(), result)
    def getVars(self):
        return self.num.getVars()

class Neg(UnaryArithmetic):
    def __init__(self, num):
        super().__init__('-', num)

class Logical(nonLeaf):
    def __init__(self, op, args):
        for i in range(len(args)):
             if not(args[i].getType() == Type.BOOL):
                 raise TypeError()
        self.args = args 
        super().__init__(op, Type.BOOL, args)
    def getVars(self):
        variables = []
        for i in range(len(self.args)):
             variables += self.args[i].getVars()
        return variables

class And(Logical):
    def __init__(self, *args):
        super().__init__('and', args)

class Or(Logical):
    def __init__(self, *args):
        super().__init__('or', args)

class Implies(Logical):
    def __init__(self, left, right):
        super().__init__('=>', [left, right])

class Beq(Logical):
    def __init__(self, left, right):
        super().__init__('=', [left, right])

class Not(Logical):
    def __init__(self, prop):
        super().__init__('not', [prop])

class Integral(nonLeaf):
    pass

class Forall(nonLeaf):
    pass

def removeDup(variables):
    i = 0
    while i < len(variables) - 1:
        for j in range(i+1, len(variables)):
            if variables[i].getType() == variables[j].getType() and str(variables[i]) == str(variables[j]):
                del variables[i]
                i -= 1
                break
        i += 1
    return variables

class stateDeclare:
    def __init__(self, name, k):
        self.start = []
        self.end = []
        for i in range(k+1):
            self.start.append(Real((name + '_' + str(i) + '_0')))
            self.end.append(Real((name + '_' + str(i) + '_t')))
    def startVar(self):
        return self.start
    def endVar(self):
        return self.end








