import enum

@enum.unique
class Type(enum.Enum):
    Bool, Int, Real = range(3)

def Sqrt(a):
    return a ** RealVal(0.5)

class Node:
    def __init__(self, nodeType):
        self.nodeType = nodeType
    def __sub__(self, num):
        return Minus(self, num)
    def __add__(self, num):
        return Plus(self, num)
    def __mul__(self, num):
        return Mul(self, num)
    def __pow__(self, num):
        return Pow(self, num)
    def __truediv__(self, num):
        return Div(self, num)
    def __eq__(self, num):
        if num.getType() == Type.Bool:
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

class Leaf(Node):
    def size(self):
        return 0

class ArithRef(Leaf):
    pass

class Constant(Leaf):
    def __init__(self, constType, value):
        super().__init__(constType)
        self.value = value
    def __repr__(self):
        return str(self.value)
    def substitution(self, subDict):
        return self
    def getVars(self):
        return set()
    def nextSub(self, subDict):
        return self

class BoolVal(Constant):
    def __init__(self, value):
        if not(isinstance(value, bool)):
           raise TypeError()
        super().__init__(Type.Bool, 'true' if value == True else 'false')

class RealVal(Constant, ArithRef):
    def __init__(self, value):
        super().__init__(Type.Real, value)


class IntVal(Constant, ArithRef):
    def __init__(self, value):
        super().__init__(Type.Int, value)

class Variable(Leaf):
    def __init__(self, varType, varId):
        super().__init__(varType)
        self.id = varId
    def __hash__(self):
        return hash(str(self.id))
    def __repr__(self):
        return str(self.id)
    def substitution(self, subDict):
        op = {Type.Bool: Bool, Type.Real: Real, Type.Int: Int}
        if self.id in subDict.keys():
            return op[self.getType()](subDict[self.id])
        else:
            return self
    def nextSub(self, subDict):
        return self
    def getVars(self):
        return {self}

class NextVar(Variable):
    def __init__(self, var):
        self.var = var
        super().__init__(self.var.getType(), var.id)
    def substitution(self, subDict):
        return self
    def nextSub(self, subDict):
        return super().substitution(subDict)

class Bool(Variable):
    def __init__(self, id):
        super().__init__(Type.Bool, id)
 
class Real(Variable, ArithRef):
    def __init__(self, id):
        super().__init__(Type.Real, id)
        
class Int(Variable, ArithRef):
    def __init__(self, id):
        super().__init__(Type.Int, id)
        

class nonLeaf(Node):
    def __init__(self, op, nonLeafType, args):
        self.op = op
        self.children = args
        super().__init__(nonLeafType)
    def __hash__(self):
        return hash(str(self))
    def size(self):
        return 1 + sum([c.size() for c in self.children])
    def __repr__(self):
        return '(' + self.op + ' ' + ' '.join([str(c) for c in self.children]) + ')'
    def getVars(self):
        return set().union(*[c.getVars() for c in self.children])

class _UnaryOp:
    def child(self):
        return self.children[0]

class _BinaryOp:
    def left(self):
        return self.children[0]
    def right(self):
        return self.children[1]


class RealFunction(nonLeaf):
    def __init__(self, name, *args):
        super().__init__(name, Type.Real, args)


class Relational(nonLeaf,_BinaryOp):
    def __init__(self, op, left, right):
        if not(left.getType() == right.getType() == Type.Int or left.getType() == right.getType() == Type.Real):
            raise TypeError()
        super().__init__(op, Type.Bool, [left, right]) 
    def substitution(self, subDict):
        opdict = {'>=': Ge, '>': Gt, '<=': Le, '<': Lt, '=': Numeq}
        return opdict[self.op](self.left().substitution(subDict), self.right().substitution(subDict))
    def nextSub(self, subDict):
        opdict = {'>=': Ge, '>': Gt, '<=': Le, '<': Lt, '=': Numeq}
        return opdict[self.op](self.left().nextSub(subDict), self.right().nextSub(subDict))

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


class BinaryArithmetic(nonLeaf,_BinaryOp):
    def __init__(self, op, left, right):
        if not(left.getType() == right.getType() == Type.Int or left.getType() == right.getType() == Type.Real):
            raise TypeError()
        super().__init__(op, left.getType(), [left, right])
    def substitution(self, subDict):
        opdict = {'^': Pow, '+': Plus, '-': Minus, '*': Mul, '/': Div}
        return opdict[self.op](self.left().substitution(subDict), self.right().substitution(subDict))
    def nextSub(self, subDict):
        opdict = {'^':Pow, '+': Plus, '-': Minus, '*': Mul, '/': Div}
        return opdict[self.op](self.left().nextSub(subDict), self.right().nextSub(subDict))

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

class Pow(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('^', left, right)


class UnaryArithmetic(nonLeaf,_UnaryOp):
    def __init__(self, op, num):
        if not(num.getType() == Type.Int or num.getType() == Type.Real):
            raise TypeError()
        super().__init__(op, num.getType(), [num])

class Neg(UnaryArithmetic):
    def __init__(self, num):
        super().__init__('-', num)
    def substitution(self, subDict):
        return Neg(self.child().substitution(subDict))
    def nextSub(self, subDict):
        return Neg(self.child().nextSub(subDict))

class Logical(nonLeaf):
    def __init__(self, op, args:list):
        for a in args:
            if not(a.getType() == Type.Bool):
                 raise TypeError()
        super().__init__(op, Type.Bool, args) 

class And(Logical):
    def __init__(self, *args):
        super().__init__('and', args)
    def substitution(self, subDict):
        subargs = [element.substitution(subDict) for element in self.children]
        return And(*subargs)
    def nextSub(self, subDict):
        subargs = [element.nextSub(subDict) for element in self.children]
        return And(*subargs) 

class Or(Logical):
    def __init__(self, *args):
        super().__init__('or', args)
    def substitution(self, subDict):
        subargs = [element.substitution(subDict) for element in self.children]
        return Or(*subargs)
    def nextSub(self, subDict):
        subargs = [element.nextSub(subDict) for element in self.children]
        return Or(*subargs)

class Implies(Logical,_BinaryOp):
    def __init__(self, left, right):
        super().__init__('=>', [left, right])
    def substitution(self, subDict):
        return Implies(self.left().substitution(subDict), self.right().substitution(subDict))
    def nextSub(self, subDict):
        return Implies(self.left().nextSub(subDict), self.right().nextSub(subDict))

class Beq(Logical,_BinaryOp):
    def __init__(self, left, right):
        super().__init__('=', [left, right])
    def substitution(self, subDict):
        return Beq(self.left().substitution(subDict), self.right().substitution(subDict))
    def nextSub(self, subDict):
        return Beq(self.left().nextSub(subDict), self.right().nextSub(subDict))

class Not(Logical,_UnaryOp):
    def __init__(self, prop):
        super().__init__('not', [prop])
    def substitution(self, subDict):
        return Not(self.child().substitution(subDict))
    def nextSub(self, subDict):
        return Not(self.child().nextSub(subDict))


class Integral(Node):
    def __init__(self, endList, startList, time, index, ode):
        self.startList = []
        self.endList = []
        for i in endList.keys():
            self.startList.append(startList[i])
            self.endList.append(endList[i])
        self.ode = ode
        self.time = time
        self.flowIndex = str(index)
        super().__init__(Type.Bool)
    def __repr__(self):
        start = '[' + ' '.join([str(sl) for sl in self.startList]) + ']'
        end   = '[' + ' '.join([str(el) for el in self.endList])   + ']'
        result = '(= ' + end + '\n  (integral 0. ' + str(self.time) + ' ' + start + ' flow_' + self.flowIndex + '))\n'
        return result
    def getVars(self):
        return set(self.startList + self.endList + [self.time])
    def substitution(self, subDict):
        return self
    def nextSub(self, subDict):
        return self
    def size(self):
        return 1

class Solution(Node):
    def __init__(self, endList, startList, index, ode):
        self.startList = []
        self.endList = []
        for i in endList.keys():
            self.startList.append(startList[i])
            self.endList.append(endList[i])
        self.ode = ode
        self.flowIndex = str(index)
        super().__init__(Type.Bool)
    def __repr__(self):
        start = '[' + ' '.join([str(sl) for sl in self.startList]) + ']'
        end   = '[' + ' '.join([str(el) for el in self.endList])   + ']'
        result = '(= ' + end + '\n  (solution flow_' + self.flowIndex + '))\n'
        return result
    def getVars(self):
        return set(self.startList + self.endList)
    def substitution(self, subDict):
        return self
    def nextSub(self, subDict):
        return self
    def size(self):
        return 1

class Forall(Node):
    def __init__(self, flowIndex, time, condition, start, end, mode):
        self.flowIndex = str(flowIndex)
        self.time = time
        self.condition = condition
        self.startDict = start
        self.endDict = end
        self.modeDict = mode
        super().__init__(Type.Bool)
    def __repr__(self):
        if not self.condition.getVars():
            result = ""
        elif str(list(self.condition.getVars())[0]) in self.modeDict.keys():
            subCondition = self.condition.substitution(self.modeDict)
            result = str(subCondition)
        else:
            endCond = self.condition.substitution(self.endDict)
            startCond = self.condition.substitution(self.startDict)
            constraint = And(endCond, startCond).substitution(self.modeDict)
            result = '(and ' + str(constraint) + ' (forall_t ' + self.flowIndex + ' [0. ' + str(self.time) + '] ' + str(endCond.substitution(self.modeDict)) + '))'
        return result
    def getVars(self):
        return set()
    def substitution(self, subDict):
        return self
    def nextSub(self, subDict):
        return self
    def size(self):
        return 1


