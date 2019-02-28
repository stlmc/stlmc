class Variable:
     def __init__(self, varType, varId):
         self.type = varType
         self.varId
     def getVariable(self):
         return {'bool' : Bool, 'int' : Int, 'real' : Real}[self.type](self.varId)
     def __str__(self):
         return self.varId


class Mode(Variable):
     def __init__(self, varType, varId):
         super().__init__(varType, varId)

class ContVar:
     def __init__(self, interval, varId):
         super().__init__("Real", varId)
         self.leftend = interval[0]
         self.left = interval[1]
         self.righ = interval[2]
         self.rightend = interval[3]

     def getInterval(self):
         return ('[' if self.leftend else '(') + repr(self.left) + ',' + repr(self.right) + (']' if self.rightend else ')')

class BinaryExp:
     def __init__(self, op, left, right):
         self.op = op
         self.left = float(left) if isinstance(left, str) else left.getVariable()
         self.right = float(right) if isinstance(right, str) else right.getVariable()
     def __str__(self):
         return self.left + self.op + self.right
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
 
 
class StlMC:
     def __init__(self, modeVar, contVar, modeModule, init, goal):
         self.modeVar = modeVar
         self.contVar = contVar
         self.modeModule = modeModule
         self.init = init
         self.goal = goal
 
    

