class Variable:
     def __init__(self, varType, varId):
         self.type = varType
         self.varId
     def getVariable(self):
         return {'bool' : Bool, 'int' : Int, 'real' : Real}[self.type](self.varId)
     def __repr__(self):
         return str(self.varId)


class Mode(Variable):
     def __init__(self, varType, varId):
         super().__init__(varType, varId)
     def __repr__(self):
         return str(varType) + str(varId)

class ContVar:
     def __init__(self, interval, varId):
         super().__init__("Real", varId)
         self.leftend = interval[0]
         self.left = interval[1]
         self.righ = interval[2]
         self.rightend = interval[3]
     def __repr__(self):
         return "Real " + ('[' if self.leftend else '(') + repr(self.left) + ',' + repr(self.right) + (']' if self.rightend else ')')
     def getInterval(self):
         return ('[' if self.leftend else '(') + repr(self.left) + ',' + repr(self.right) + (']' if self.rightend else ')')

class BinaryExp:
     def __init__(self, op, left, right):
         self.op = op
         self.left = float(left) if isinstance(left, str) else left.getVariable()
         self.right = float(right) if isinstance(right, str) else right.getVariable()
     def __repr__(self):
         return str(self.left) + str(self.op) + str(self.right)
     def getExpression(self):
         if self.op == '+':
             return self.left + self.right
         elif self.op == '-':
             return self.left - self.right
         elif self.op == '*':
             return self.left * self.right
         elif self.op == '/':
             return self.left / self.right
         else:
             raise "Not yet in Binary Expression"

class CompCond:
     def __init__(self, op, left, right):
         self.op = op
         self.left = float(left) if isinstance(left, str) else left.getVariable()
         self.right = float(right) if isinstance(right, str) else right.getVariable()
     def __repr__(self):
         return str(self.left) + str(self.op) + str(self.right)
     def getExpression(self):
         if op == '<':
             return self.left < self.right
         elif op == '<=':
             return self.left <= self.right
         elif op == '>':
             return self.left > self.right
         elif op == '>=':
             return self.left >= self.right
         elif op == '==':
             return self.left == self.right
         elif op == '!=':
             return self.left != self.right
         else:
             raise "Not yet in Compare Condition"
class Multy:
    def __init__(self, op, props):
        self.op = op
        self.props = props
    def __repr__(self):
        strProps = ''.join(self.props)
        return str(self.op) + strProps
    def getExpression(self):
        return {'and' : And, 'or' : Or}[self.op](*self.props)

class Unary:
    def __init__(self, op, prop):
        self.op = op
        self.prop = prop
    def __repr__(self):
        return str(self.op) + repr(self.prop)
    def getExpression(self):
        return {'not' : Not}[self.op](self.prop)

class MultiCond(Multy):
    pass

class UnaryCond(Unary):
    pass

class MultiJump(Multy):
    pass

class UnaryJump(Unary):
    pass

class DiffEq:
    def __init__(self, contVar, flow):
        self.contVar = contVar
        self.flow = flow
    def getExpression(self):
        result = dict()
        result[self.contVar] = self.flow
        return result

class SolEq:
    def __init__(self, contVar, Sol):
        self.contVar = contVar
        self.sol = Sol
    def getExpressiont(self):
        result = dict()
        resutl[self.contVar] = self.sol
        return result

class modeModule:
    def __init__(self, mode, inv, flow, jump):
        self.mode = mode
        self.inv = inv
        self.flow = flow
        self.jump = jump
    def getMode(self):
        return self.mode
    def getInv(self):
        return self.inv
    def getFlow(self):
        return(self.flow)
    def getJump(self):
        return(self.jump)

class flowDecl:
    def __init__(self, expType, exps):
        self.type = expType   # empty : wrong, diff : diff_eq(), sol : sol_eq()
        self.exps = exps
    
class jumpDecl:
    def __init__(self, cond, jumpRedecl):
        self.cond = cond
        self.jumpRedcl =jumpRedecl


 

class StlMC:
     def __init__(self, modeVar, contVar, modeModule, init, goal):
         self.modeVar = modeVar
         self.contVar = contVar
         self.modeModule = modeModule
         self.init = init
         self.goal = goal
 
    

