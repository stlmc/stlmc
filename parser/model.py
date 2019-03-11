import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))

from core.constraint import *

def isNumber(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

class Variable:
     def __init__(self, varType, varId):
         self.type = varType
         self.varId = varId
     def getVariable(self):
         return {'bool' : Bool, 'int' : Int, 'real' : Real}[self.type](self.varId)
     def __repr__(self):
         return str(self.type) + " " + str(self.varId)
     def getVarString(self):
         return str(self.type) + " " + str(self.varId)
     def getType(self):
         return str(self.type)
     def getId(self):
         return str(self.varId)

class Mode(Variable):
     def __init__(self, varType, varId):
         super().__init__(varType, varId)
         
class ContVar(Variable):
     def __init__(self, interval, varId):
         super().__init__("real", varId)
         self.leftend = interval[0]
         self.left = interval[1]
         self.right = interval[2]
         self.rightend = interval[3]
     def __repr__(self):
         return super(ContVar,self).getVarString() + (' [' if self.leftend else ' (') + repr(self.left) + ',' + repr(self.right) + (']' if self.rightend else ')')
     def getConstraint(self):
         variable =  {'bool' : Bool, 'int' : Int, 'real' : Real}[self.type](self.varId)
         consts = list()
         if self.leftend:
             consts.append(variable >= RealVal(float(self.left)))
         else:
             consts.append(variable > RealVal(float(self.left)))
         if self.rightend:
             consts.append(variable <= RealVal(float(self.right)))
         else:
             consts.append(variable < RealVal(float(self.right)))
         return And(*consts) 

class BinaryExp:
     def __init__(self, op, left, right):
         self.op = op
         self.left = left
         self.right = right
         if isinstance(left, str) and isinstance(right, str):
             self.left = float(left) if isNumber(left) else left
             self.right = float(right) if isNumber(right) else right
     def __repr__(self):
         return str(self.left) + str(self.op) + str(self.right)
     def getExpression(self, varDict):
         left = self.left 
         right = self.right
         if str(self.left) in varDict.keys(): 
             left = varDict[str(self.left)]
         if str(self.right) in varDict.keys():
            right = varDict[str(self.right)]
         if self.op == '+':
             return left + right
         elif self.op == '-':
             return left - right
         elif self.op == '*':
             return left * right
         elif self.op == '/':
             return left / right
         else:
             raise "Not yet in Binary Expression"
     def getType(self):
         return Type.Real

class CompCond:
     def __init__(self, op, left, right):
         self.op = op
         self.left = left
         self.right = right
         if isinstance(left, str) and isinstance(right, str):
             self.left = float(left) if isNumber(left) else left
             self.right = float(right) if isNumber(right) else right
     def __repr__(self):
         return str(self.left) + str(self.op) + str(self.right)
     def getExpression(self, varDict):
         left = self.left 
         right = self.right
         if str(self.left) in varDict.keys():
             left = varDict[str(self.left)]
         if str(self.right) in varDict.keys():
            right = varDict[str(self.right)]
         if self.op == '<':
             return left < right
         elif self.op == '<=':
             return left <= right
         elif self.op == '>':
             return left > right
         elif self.op == '>=':
             return left >= right
         elif self.op == '==':
             return left == right
         elif self.op == '!=':
             return left != right
         else:
             raise "Not yet in Compare Condition"
     def getType(self):
         return Type.Bool

class Multy:
    def __init__(self, op, props):
        self.op = op
        self.props = props
    def __repr__(self):
        strProps = ''.join(str(self.props))
        return str(self.op) + " " + strProps
    def getExpression(self, varDict):
        result = list()
        for i in range(len(self.props)):
            result.append(self.props[i].getExpression(varDict))
        return {'and' : And, 'or' : Or}[self.op](*result)

class Unary:
    def __init__(self, op, prop):
        self.op = op
        self.prop = prop
    def __repr__(self):
        return str(self.op) + " " + repr(self.prop)
    def getExpression(self, varDict):
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
    def __repr__(self):
        return str(self.contVar) + " = " + str(self.flow)
    def getExpression(self):
        result = dict()
        result[self.contVar] = self.flow
        return result

class SolEq:
    def __init__(self, contVar, Sol):
        self.contVar = contVar
        self.sol = Sol
    def __repr__(self):
        return str(self.contVar) + " = " + str(self.sol)
    def getExpression(self):
        result = dict()
        resutl[self.contVar] = self.sol
        return result

class modeModule:
    def __init__(self, mode, inv, flow, jump):
        self.mode = mode
        self.inv = inv
        self.flow = flow
        self.jump = jump
    def __repr__(self):
        return str(self.mode) + "\n" + str(self.inv) + "\n" + str(self.flow) + "\n" + str(self.jump)
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
    def __repr__(self):
        return str(self.type) + " " +  str(self.exps)
   
class jumpRedeclModule:
    def __init__(self, cond, jumpRedecl):
        self.cond = cond
        self.jumpRedecl =jumpRedecl
    def __repr__(self):
        return str(self.cond) + " " + str(self.jumpRedecl)

class jumpDecl:
    def __init__(self, redeclList):
        self.redeclList = redeclList
    def __repr__(self):
        return str(self.redeclList)

class jumpMod:
      def __init__(self, nextVarId, exp):
          self.nextVarId = nextVarId
          self.exp = exp
      def __repr__(self):
          return str(self.nextVarId) + "' = " + str(self.exp)

class propDecl:
    def __init__(self, varId, cond):
        self.id = varId
        self.cond = cond
    def __repr__(self):
        return str(self.id) + " = " + str(self.cond)

class formulaDecl:
    def __init__(self, formulaList):
        self.formulaList = formulaList  # string type formulas
    def getFormulas(self):
        return self.formulaList 

class StlMC:
     def __init__(self, modeVar, contVar, modeModule, init, prop, goal):
         self.modeVar = modeVar
         self.contVar = contVar
         self.modeModule = modeModule
         self.init = init
         self.prop = prop    #list type
         self.goal = goal
         self.subvars = self.makeVariablesDict()

     def makeVariablesDict(self):
         result = dict()
         for i in range(len(self.modeVar)):
             result[str(self.modeVar[i].getId())] = {'bool' : Bool, 'int' : Int, 'real' : Real}[self.modeVar[i].getType()](self.modeVar[i].getId())
         for i in range(len(self.contVar)):
             result[str(self.contVar[i].getId())] = {'bool' : Bool, 'int' : Int, 'real' : Real}[self.contVar[i].getType()](self.contVar[i].getId())
         result['false'] = BoolVal(False)
         result['true'] = BoolVal(True)
         return result

     def makeVarRangeConsts(self):
         result = list()
         for i in range(len(self.contVar)):
             result.append(self.contVar[i].getConstraint())
         return result

     def modelConstraints(self):
         result = list()
         result.append(self.makeVarRangeConsts())
         return result

     def reach(self):
         print(self.init.getExpression(self.subvars))

         '''
         for i in range(len(self.modeVar)):
             print(self.modeVar[i])
         for i in range(len(self.contVar)):
             print(self.contVar[i])
         for i in range(len(self.modeModule)):
             print(self.modeModule[i]) 
         '''
         print("construct stlMC object") 
    

