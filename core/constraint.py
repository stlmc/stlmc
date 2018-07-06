import enum

@enum.unique
class Type(enum.Enum):
    Bool, Int, Real = range(3)

def Sqrt(a):
    return a * RealVal(0.5)

class Node:
    def __init__(self, nodeType):
        self.nodeType = nodeType
    def __sub__(self, num):
        return Minus(self, num)
    def __add__(self, num):
        return Plus(self, num)
    def __mul__(self, num):
        return Mul(self, num)
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
        self.value = 'true' if value == True else 'false'
        super().__init__(Type.Bool, self.value)

class RealVal(Constant, ArithRef):
    def __init__(self, value):
        self.value = value
        super().__init__(Type.Real, value)

class cos(Constant):
    def __init__(self, value):
        self.value = value
        super().__init__(Type.Real, value)
    def __repr__(self):
        return '(cos ' + str(self.value) + ')'

class sin(Constant):
    def __init__(self, value):
        self.value = value
        super().__init__(Type.Real, value)
    def __repr__(self):
        return '(sin ' + str(self.value) + ')'

class tan(Constant):
    def __init__(self, value):
        self.value = value
        super().__init__(Type.Real, value)
    def __repr__(self):
        return '(tan ' + str(self.value) + ')'


class IntVal(Constant, ArithRef):
    def __init__(self, value):
        self.value = value
        super().__init__(Type.Int, value)

class Variable(Leaf):
    def __init__(self, varType, var):
        super().__init__(varType)
        self.var = var
        self.id = var.id
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
    def getVars(self):
        return set([self.var])

class NextVar(Variable):
    def __init__(self, var):
        self.var = var
        self.id = var.id
        super().__init__(self.var.getType(), self)
    def nextSub(self, subDict):
        op = {Type.Bool: Bool, Type.Real: Real, Type.Int: Int}
        if self.id in subDict.keys():
            return op[self.getType()](subDict[self.id])
        else:
            return self
    def substitution(self, subDict):
        return self

class Bool(Variable):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.Bool, self)
    def nextSub(self, subDict):
        return self
 
class Real(Variable, ArithRef):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.Real, self)
    def nextSub(self, subDict):
        return self
        
class Int(Variable, ArithRef):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.Int, self)
    def nextSub(self, subDict):
        return self
        
class nonLeaf(Node):
    def __init__(self, op, nonLeafType, args):
        self.op = op
        self.children = args
        super().__init__(nonLeafType)
    def __hash__(self):
        return hash(str(self))
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
        if not(left.getType() == right.getType() == Type.Int or left.getType() == right.getType() == Type.Real):
            raise TypeError()
        self.left = left
        self.right = right
        self.op = op
        super().__init__(op, Type.Bool, [left, right]) 
    def getVars(self):
        return self.left.getVars() | self.right.getVars()
    def substitution(self, subDict):
        opdict = {'>=': Ge, '>': Gt, '<=': Le, '<': Lt, '=': Numeq}
        return opdict[self.op](self.left.substitution(subDict), self.right.substitution(subDict))
    def nextSub(self, subDict):
        opdict = {'>=': Ge, '>': Gt, '<=': Le, '<': Lt, '=': Numeq}
        return opdict[self.op](self.left.nextSub(subDict), self.right.nextSub(subDict))

class Ge(Relational):
    def __init__(self, left, right):
        super().__init__('>=', left, right)
        self.left = left
        self.right = right

class Gt(Relational):
    def __init__(self, left, right):
        super().__init__('>', left, right)
        self.left = left
        self.right = right

class Le(Relational):
    def __init__(self, left, right):
        super().__init__('<=', left, right)
        self.left = left
        self.right = right

class Lt(Relational):
    def __init__(self, left, right):
        super().__init__('<', left, right)
        self.left = left
        self.right = right

class Numeq(Relational):
    def __init__(self, left, right):
        super().__init__('=', left, right)
        self.left = left
        self.right = right


class BinaryArithmetic(nonLeaf):
    def __init__(self, op, left, right):
        if not(left.getType() == right.getType() == Type.Int or left.getType() == right.getType() == Type.Real):
            raise TypeError()
        self.left = left
        self.right = right
        self.op = op
        super().__init__(op, left.getType(), [left, right])
    def getVars(self):
        return self.left.getVars() | self.right.getVars()
    def substitution(self, subDict):
        opdict = {'+': Plus, '-': Minus, '*': Mul, '/': Div}
        return opdict[self.op](self.left.substitution(subDict), self.right.substitution(subDict))
    def nextSub(self, subDict):
        opdict = {'+': Plus, '-': Minus, '*': Mul, '/': Div}
        return opdict[self.op](self.left.nextSub(subDict), self.right.nextSub(subDict))

class Plus(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('+', left, right)
        self.left = left
        self.right = right


class Minus(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('-', left, right)
        self.left = left
        self.right = right


class Mul(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('*', left, right)
        self.left = left
        self.right = right

class Div(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('/', left, right)
        self.left = left
        self.right = right


class UnaryArithmetic(nonLeaf):
    def __init__(self, op, num):
        if not(num.getType() == Type.Int or num.getType() == Type.Real):
            raise TypeError()
        self.num = num
        if num.getType() == Type.Int:
            result = [InTVal(0), num]
        else:
            result = [RealVal(0), num]
        super().__init__(op, num.getType(), result)
    def getVars(self):
        return self.num.getVars()

class Neg(UnaryArithmetic):
    def __init__(self, num):
        super().__init__('-', num)
        self.num = num
    def substitution(self, subDict):
        return Neg(self.num.substitution(subDict))
    def nextSub(self, subDict):
        return Neg(self.num.nextSub(subDict))

class Logical(nonLeaf):
    def __init__(self, op, args):
        unnested = []
        for i in range(len(args)):
            if isinstance(args[i], list):
                unnested += args[i]
            else:
                unnested.append(args[i])
        for i in range(len(unnested)):
             if not(unnested[i].getType() == Type.Bool):
                 raise TypeError()
        self.args = unnested
        super().__init__(op, Type.Bool, self.args) 
    def getVars(self):
        variables = set()
        for i in range(len(self.args)):
             variables = variables.union(self.args[i].getVars())
        return variables

class And(Logical):
    def __init__(self, *args):
        self.args = list(args)
        super().__init__('and', self.args)
    def __repr__(self):
        result = '(and '
        for i in range(len(self.args)):
            result += str(self.args[i])
            if i != len(self.args)-1:
                result += ' '
        result += ')'
        return result
    def substitution(self, subDict):
        subargs = [element.substitution(subDict) for element in self.args]
        return And(*subargs)
    def nextSub(self, subDict):
        subargs = [element.nextSub(subDict) for element in self.args]
        return And(*subargs) 

class Or(Logical):
    def __init__(self, *args):
        self.args = list(args)
        super().__init__('or', self.args)
    def __repr__(self):
        result = '(or '
        for i in range(len(self.args)):
            result += str(self.args[i])
            if i != len(self.args)-1:
                result += ' '
        result += ')'
        return result
    def substitution(self, subDict):
        subargs = [element.substitution(subDict) for element in self.args]
        return Or(*subargs)
    def nextSub(self, subDict):
        subargs = [element.nextSub(subDict) for element in self.args]
        return Or(*subargs)

class Implies(Logical):
    def __init__(self, left, right):
        super().__init__('=>', [left, right])
        self.left = left
        self.right = right
    def __repr__(self):
        result = '(=> ' + str(self.left) + ' ' + str(self.right) + ')\n       '
        return result
    def substitution(self, subDict):
        return Implies(self.left.substitution(subDict), self.right.substitution(subDict))
    def nextSub(self, subDict):
        return Implies(self.left.nextSub(subDict), self.right.nextSub(subDict))

class Beq(Logical):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        super().__init__('=', [left, right])
    def __repr__(self):
        result = '(= ' + str(self.left) + ' ' + str(self.right) + ')\n       '
        return result
    def substitution(self, subDict):
        return Beq(self.left.substitution(subDict), self.right.substitution(subDict))
    def nextSub(self, subDict):
        return Beq(self.left.nextSub(subDict), self.right.nextSub(subDict))

class Not(Logical):
    def __init__(self, prop):
        super().__init__('not', [prop])
        self.prop = prop
    def __repr__(self):
        result = '(not ' + str(self.prop) + ')\n       '
        return result
    def substitution(self, subDict):
        return Not(self.prop.substitution(subDict))
    def nextSub(self, subDict):
        return Not(self.prop.nextSub(subDict))

class Integral(nonLeaf):
    def __init__(self, endList, startList, time, index, ode):
        self.startList = []
        self.endList = []
        for i in endList.keys():
            self.startList.append(startList[i])
            self.endList.append(endList[i])
        self.ode = ode
        self.time = time
        self.flowIndex = str(index)
        super().__init__('integral', Type.Bool, [self])
    def __repr__(self):
        start = '['
        end = '['
        for i in range(len(self.endList)):
            start += str(self.startList[i])
            end += str(self.endList[i])
            if i != len(self.endList) - 1:
               start += ' '
               end += ' '
        start += ']'
        end += ']'
        result = '(= ' + end + '\n  (integral 0. ' + str(self.time) + ' ' + start + ' flow_' + self.flowIndex + '))\n'
        return result
    def getVars(self):
        return set(self.startList + self.endList)
    def substitution(self, subDict):
        return self
    def nextSub(self, subDict):
        return self

class Forall(nonLeaf):
    def __init__(self, flowIndex, time, condition, start, end, mode):
        self.flowIndex = str(flowIndex)
        self.time = time
        self.condition = condition
        self.startDict = start
        self.endDict = end
        self.modeDict = mode
        super().__init__('forall', Type.Bool, [self])
    def __repr__(self):
        typeList = [i.getType() for i in self.condition.getVars()]
        if not(Type.Real in typeList):
            subCondition = self.condition.substitution(self.modeDict)
            result = str(subCondition)
        else:
            endCond = self.condition.substitution(self.endDict)
            startCond = self.condition.substitution(self.startDict)
            constraint = And(endCond, startCond)
            result = '(and ' + str(constraint) + ' (forall_t ' + self.flowIndex + ' [0. ' + str(self.time) + '] ' + str(self.condition.substitution(self.endDict)) + '))'
        return result
    def getVars(self):
        return set()
    def substitution(self, subDict):
        return self
    def nextSub(self, subDict):
        return self


