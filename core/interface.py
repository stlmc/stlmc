from .error import *
from .TYPE import *
import z3

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

class ArithRef(Leaf):
    pass

class Constant(Leaf):
    def __init__(self, constType, value):
        super().__init__(constType, [])
        self.value = value
    def __repr__(self):
        return str(self.value)
    def substitution(self, subDict):
        return self

class BoolVal(Constant):
    def __init__(self, value):
        if not(isinstance(value, bool)):
           raise TypeError()
        self.value = 'true' if value == True else 'false'
        super().__init__(Type.BOOL, self.value)
    def z3Obj(self):
        if self.value == 'true':
            return z3.BoolVal(True)
        else:
            return z3.BoolVal(False)        
        return z3.BoolVal(str(self.value))        

class RealVal(Constant, ArithRef):
    def __init__(self, value):
        self.value = value
        super().__init__(Type.REAL, value)
    def z3Obj(self):
        return z3.RealVal(str(self.value))

class IntVal(Constant, ArithRef):
    def __init__(self, value):
        self.value = value
        super().__init__(Type.INT, value)
    def z3Obj(self):
        return z3.IntVal(str(self.value))

class Variable(Leaf):
    def __init__(self, varType, var):
        super().__init__(varType, [var])
        self.var = var
        self.id = var.id
    def __hash__(self):
        return hash(self.id)
    def __repr__(self):
        return str(self.var)
    
class Bool(Variable):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.BOOL, self)
    def __repr__(self):
        return str(self.id)
    def z3Obj(self):
        return z3.Bool(str(self.id))
    def substitution(self, subDict):
        if self.id in subDict.keys():
           return Bool(subDict[self.id])
        else:
            return self
 
class Real(Variable, ArithRef):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.REAL, self)
    def __repr__(self):
        return str(self.id)
    def z3Obj(self):
        return z3.Real(str(self.id))
    def substitution(self, subDict):
        if self.id in subDict.keys():
           return Real(subDict[self.id])
        else:
            return self

class Int(Variable, ArithRef):
    def __init__(self, id):
        self.id = id
        super().__init__(Type.INT, self)
    def __repr__(self):
        return str(self.id)
    def z3Obj(self):
        return z3.Int(str(self.id))
    def substitution(self, subDict):
        if self.id in subDict.keys():
           return Int(subDict[self.id])
        else:
            return self

class nonLeaf(Node):
    def __init__(self, op, nonLeafType, args):
        self.op = op
        self.children = []
        if isinstance(args, Forall) or isinstance(args, Integral):
            self.children.append(args)
        else:
            self.children += args
        variables = []
        if not(isinstance(args, Forall) or isinstance(args, Integral)):
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
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x >= y
    def substitution(self, subDict):
        return Ge(self.left.substitution(subDict), self.right.substitution(subDict))

class Gt(Relational):
    def __init__(self, left, right):
        super().__init__('>', left, right)
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x > y
    def substitution(self, subDict):
        return Gt(self.left.substitution(subDict), self.right.substitution(subDict))

class Le(Relational):
    def __init__(self, left, right):
        super().__init__('<=', left, right)
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x <= y
    def substitution(self, subDict):
        return Le(self.left.substitution(subDict), self.right.substitution(subDict))

class Lt(Relational):
    def __init__(self, left, right):
        super().__init__('<', left, right)
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x < y
    def substitution(self, subDict):
        return Lt(self.left.substitution(subDict), self.right.substitution(subDict))

class Numeq(Relational):
    def __init__(self, left, right):
        super().__init__('=', left, right)
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x == y
    def substitution(self, subDict):
        return Numeq(self.left.substitution(subDict), self.right.substitution(subDict))

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
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x + y
    def substitution(self, subDict):
        return Plus(self.left.substitution(subDict), self.right.substitution(subDict))

class Minus(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('-', left, right)
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x - y
    def substitution(self, subDict):
        return Minus(self.left.substitution(subDict), self.right.substitution(subDict))

class Mul(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('*', left, right)
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x * y
    def substitution(self, subDict):
        return Mul(self.left.substitution(subDict), self.right.substitution(subDict))

class Div(BinaryArithmetic):
    def __init__(self, left, right):
        super().__init__('/', left, right)
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x / y
    def substitution(self, subDict):
        return Div(self.left.substitution(subDict), self.right.substitution(subDict))

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
        self.num = num
    def z3Obj(self):
        x = self.num.z3Obj()
        return -x
    def substitution(self, subDict):
        return Neg(self.num.substitution(subDict))

class Logical(nonLeaf):
    def __init__(self, op, args):
        unnested = []
        for i in range(len(args)):
            if isinstance(args[i], list):
                unnested += args[i]
            else:
                unnested.append(args[i])
        for i in range(len(unnested)):
             if not(unnested[i].getType() == Type.BOOL):
                 raise TypeError()
        self.args = unnested
        super().__init__(op, Type.BOOL, self.args) 
    def getVars(self):
        variables = []
        for i in range(len(self.args)):
             variables += self.args[i].getVars()
        return variables

class And(Logical):
    def __init__(self, *args):
        self.args = []
        self.args += args
        super().__init__('and', self.args)
    def __repr__(self):
        result = '(and '
        for i in range(len(self.args)):
            result += str(self.args[i])
            if i != len(self.args)-1:
                result += ' '
        result += ')'
        return result
    def z3Obj(self):
        z3args = []
        for i in range(len(self.args)):
            z3args.append(self.args[i].z3Obj())
        return z3.And(z3args)
    def substitution(self, subDict):
        subargs = [element.substitution(subDict) for element in self.args]
        return And(*subargs)
 
class Or(Logical):
    def __init__(self, *args):
        self.args = []
        self.args += args
        super().__init__('or', args)
    def __repr__(self):
        result = '(or '
        for i in range(len(self.args)):
            result += str(self.args[i])
            if i != len(self.args)-1:
                result += ' '
        result += ')'
        return result
    def z3Obj(self):
        z3args = []
        for i in range(len(self.args)):
            z3args.append(self.args[i].z3Obj())
        return z3.Or(z3args)
    def substitution(self, subDict):
        subargs = [element.substitution(subDict) for element in self.args]
        return Or(*subargs)

class Implies(Logical):
    def __init__(self, left, right):
        super().__init__('=>', [left, right])
        self.left = left
        self.right = right
    def __repr__(self):
        result = '(=> ' + str(self.left) + ' ' + str(self.right) + ')\n       '
        return result
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return z3.Implies(x, y)
    def substitution(self, subDict):
        return Implies(self.left.substitution(subDict), self.right.substitution(subDict))

class Beq(Logical):
    def __init__(self, left, right):
        super().__init__('=', [left, right])
        self.left = left
        self.right = right
    def z3Obj(self):
        x = self.left.z3Obj()
        y = self.right.z3Obj()
        return x == y
    def substitution(self, subDict):
        return Beq(self.left.substitution(subDict), self.right.substitution(subDict))

class Not(Logical):
    def __init__(self, prop):
        super().__init__('not', [prop])
        self.prop = prop
    def z3Obj(self):
        x = self.prop.z3Obj()
        return z3.Not(x)
    def substitution(self, subDict):
        return Not(self.prop.substitution(subDict))

class Integral(nonLeaf):
    def __init__(self, endList, startList, time, ode):
        self.endList = endList
        self.startList = startList
        self.ode = ode
        self.time = time
        self.flow = ode.flow
        self.flowIndex = ode.modeID
        self.variables = ode.variables
        super().__init__('integral', Type.BOOL, self)
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
        result = '\n         (= ' + end + '\n  (integral 0. ' + str(self.time) + ' ' + start + ' ' + self.flowIndex + '))\n'
        result = '(= ' + start + '\n  (integral 0. ' + str(self.time) + ' ' + end + ' ' + self.flowIndex + '))\n'
        return result
    def z3Obj(self):
        subDict = {}
        for i in range(len(self.endList)):
            keyIndex = str(self.endList[i]).find('_')
            keyValue = str(self.endList[i])[0:keyIndex]
            subDict[keyValue] = self.startList[i]
        substitutionExp = self.ode.constantReplace(subDict)
        result = []
        for i in range(len(self.endList)):
            keyIndex = str(self.endList[i]).find('_') 
            keyValue = str(self.endList[i])[0:keyIndex]
            result.append(self.endList[i] == self.startList[i] + substitutionExp[keyValue] * self.time)
        z3result = []
        for i in range(len(result)):
            z3result.append(result[i].z3Obj())
        return z3.And(z3result) 
    def substitution(self, subDict):
        return self

class Forall(nonLeaf):
    def __init__(self, flowIndex, time, condition, start, end):
        self.flowIndex = flowIndex
        self.time = time
        self.condition = condition
        self.startDict = start
        self.endDict = end
        super().__init__('forall', Type.BOOL, self)
    def __repr__(self):
        result = '\n       (forall_t ' + str(self.flowIndex) + ' [0 ' + str(self.time) + '] ' + str(self.condition.substitution(self.endDict)) + ')'
        result = '(forall_t ' + str(self.flowIndex) + ' [0. ' + str(self.time) + '] ' + str(self.condition.substitution(self.endDict)) + ')'
        return result
    def z3Obj(self):
        endCond = self.condition.substitution(self.endDict).z3Obj()
        startCond = self.condition.substitution(self.startDict).z3Obj()
        return z3.And(endCond, startCond)
    def substitution(self, subDict):
        return self

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
        self.id = name
        for i in range(k+1):
            self.start.append(Real((name + '_' + str(i) + '_0')))
            self.end.append(Real((name + '_' + str(i) + '_t')))
    def startVar(self):
        return self.start
    def endVar(self):
        return self.end

class ODE:
    def __init__(self, modeID, flow):
        self.modeID = 'flow_' + str(modeID)
        self.flow = flow
        self.variables = flow.keys()
    def constantReplace(self, subDict):
        result = self.flow.copy()
        for i in result.keys():
            subvariables = result[i].getVars()
            for j in range(len(subvariables)):
                if (str(subvariables[j]) in self.flow.keys()):
                    if self.flow[str(subvariables[j])] == RealVal(0):
                        pass
                    else:
                        raise z3constODEerror()
                else:
                    raise z3constODEerror()
            result[i] = result[i].substitution(subDict)
        return result


class printHandler:
    def __init__(self, const, filename, varRange, defineODE):
        self.const = const
        self.defineODE = defineODE
        self.filename = filename
        self.varRange = varRange
    def varsDeclareHandler(self):
        f = open(self.filename, 'a+')
        variables = []
        for i in range(len(self.const)):
            variables += self.const[i].getVars()
        variables =removeDup(variables)
        for i in range(len(variables)):
            f.write("(declare-fun ")
            f.write(str(variables[i]))
            f.write(" () ")
            typeName = str(type(variables[i]))
            keyIndex = str(variables[i]).find('_')
            f.write(typeName[-6: -2])
            key = str(variables[i])[:keyIndex]
            if key in self.varRange.keys():
                f.write(" [" + str(self.varRange[key][0]) + ", " + str(self.varRange[key][1]) + "]")
            elif typeName[-6: -2] == 'Real':
                f.write(" [0.0000, 1000.0000]")
            f.write(")\n")
        f.close()

    def ODEDeclareHandler(self):
        f = open(self.filename, 'w')
        f.write("(set-logic QF_NRA_ODE)\n")
        for i in self.varRange.keys():
            f.write("(declare-fun ")
            f.write(i)      
            f.write(" () Real [" + str(self.varRange[i][0]) + ", " + str(self.varRange[i][1]) + "])\n")
        for i in range(len(self.defineODE)):
            f.write("(define-ode flow_" + str(i+1) + " (")
            for j in self.defineODE[i].flow.keys():
                f.write("(= d/dt[" + j + "] " + str(self.defineODE[i].flow[j]) + ")\n                 ")
            f.write("))\n")
        f.close()
    
    def assertDeclareHandler(self):
        f = open(self.filename, 'a+')
        for i in range(len(self.const)):
            f.write("(assert " + repr(self.const[i]) + ")\n")
        f.close()

    def satHandler(self):
        f = open(self.filename, 'a+')
        f.write("(check-sat)\n")
        f.close()

    
    def exitHandler(self):
        f = open(self.filename, 'a+')
        f.write("(exit)\n")
        f.close()







