import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))

from core.constraint import *
from core.stl import parseFormula
from core.z3Handler import checkSat

import core.partition as PART
import core.separation as SEP
import core.encoding as ENC

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
             self.left = RealVal(float(left)) if isNumber(left) else left
             self.right = RealVal(float(right)) if isNumber(right) else right
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
             self.left = RealVal(float(left)) if isNumber(left) else left
             self.right = RealVal(float(right)) if isNumber(right) else right
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
    def getVarId(self):
        return str(self.contVar)
    def getFlow(self):
        if type(self.flow) in [RealVal, IntVal, BoolVal]:
            return self.flow
        return self.flow.getExpression()
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
    def getVarId(self):
        return str(self.contVar)
    def getFlow(self):
        if isinstance(self.sol, str):
            return self.sol           
        return self.sol.getExpression()
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
    # return flowDecl type
    def getFlow(self):
        return(self.flow)
    # return jumpDecl type
    def getJump(self):
        return(self.jump)

class flowDecl:
    def __init__(self, expType, exps):
        self.type = expType   # empty : wrong, diff : diff_eq(), sol : sol_eq()
        self.exps = exps
    def __repr__(self):
        return str(self.type) + " " +  str(self.exps)
    def getExpression(self):
        return self.exps
 
class jumpRedeclModule:
    def __init__(self, cond, jumpRedecl):
        self.cond = cond
        self.jumpRedecl =jumpRedecl
    def __repr__(self):
        return str(self.cond) + " " + str(self.jumpRedecl)
    def getCond(self, varDict):
        condition = self.cond.getExpression(varDict)
    def getExpression(self,varDict):
        condition = self.cond.getExpression(varDict)
        redecl = self.jumpRedecl.getExpression(varDict)
        return Or(Not(condition), redecl)
    def getJumpRedecl(self):
        return self.jumpRedecl

class jumpDecl:
    def __init__(self, redeclList):
        self.redeclList = redeclList
    def __repr__(self):
        return str(self.redeclList)
    def getRedeclList(self):
        return self.redeclList

class jumpMod:
      def __init__(self, nextVarId, exp):
          self.nextVarId = nextVarId
          self.exp = exp
      def __repr__(self):
          return str(self.nextVarId) + "' = " + str(self.exp)
      def getExpression(self, varDict):
          if self.nextVarId in varDict.keys():
              left = NextVar(varDict[self.nextVarId])
              if isinstance(self.exp, BoolVal):
                  right = self.exp
              elif self.exp in varDict.keys():
                  right = varDict[self.exp]
              else:
                  right = self.exp.getExpression(varDict)
              return (left == right) 
          else:
              raise ("jump undeclared variable id in next variable handling")

class propDecl:
    def __init__(self, varId, cond):
        self.id = varId
        self.cond = cond
    def __repr__(self):
        return str(self.id) + " = " + str(self.cond)
    def getExpression(self, varDict):
        return self.cond.getExpression(varDict)
    def getId(self):
        return Bool(str(self.id))

class formulaDecl:
    def __init__(self, formulaList):
        self.formulaList = formulaList  # string type formulas
    def getFormulas(self, propDict):
        result = list()
        for i in range(len(self.formulaList)):
            curStl = parseFormula("~"+self.formulaList[i])
            result.append(curStl)
        return result

class StlMC:
    def __init__(self, modeVar, contVar, modeModule, init, prop, goal):
        self.modeVar = modeVar
        self.contVar = contVar
        self.modeModule = modeModule
        self.init = init
        self.prop = prop    #list type
        self.goal = goal
        self.subvars = self.makeVariablesDict()

    # Transform the string id to Type(id) ex: 'a' -> Bool('a')
    def makeVariablesDict(self):
        op = {'bool' : Bool, 'int' : Int, 'real' : Real}
        result = dict()
        for i in range(len(self.modeVar)):
            result[str(self.modeVar[i].getId())] = op[self.modeVar[i].getType()](self.modeVar[i].getId())
        for i in range(len(self.contVar)):
            result[str(self.contVar[i].getId())] = op[self.contVar[i].getType()](self.contVar[i].getId())
        result['false'] = BoolVal(False)
        result['true'] = BoolVal(True)
        return result

    # Substitution proposition and mode variables according to bound k: {'fonepo' : fonepo_k} 
    def makeSubMode(self, k):
        op = {'bool' : Bool, 'int' : Int, 'real' : Real}
        result = {}
        for i in range(len(self.modeVar)):
            result[str(self.modeVar[i].getId())] = op[self.modeVar[i].getType()](self.modeVar[i].getId() + '_' + str(k))
        return result

    # Substituion varialbes according to bound k, sOe: var_k_0 or var_k_t
    def makeSubVars(self, k, sOe):
        op = {'bool' : Bool, 'int' : Int, 'real' : Real}
        result = {}
        for i in range(len(self.contVar)):
            result[str(self.contVar[i].getId())] = op[self.contVar[i].getType()](self.contVar[i].getId() + '_' + str(k) + '_' + sOe)
        return result

    # Make variable range constratint
    def makeVarRangeConsts(self):
        result = list()
        for i in range(len(self.contVar)):
            result.append(self.contVar[i].getConstraint())
        return result

    def combineDict(self, dict1, dict2):
        result = dict1.copy()
        for i in dict2.keys():
            result[i] = dict2[i]
        return result

    def jumpConstraints(self, bound):
        jumpConsts = list()
        for i in range(len(self.modeModule)):
            subresult = list()
            for j in range(len(self.modeModule[i].getJump().getRedeclList())):
                subresult.append(self.modeModule[i].getJump().getRedeclList()[j].getExpression(self.subvars))
            jumpConsts.append(And(self.modeModule[i].getMode().getExpression(self.subvars), Or(*subresult)))

        result = []
        for k in range(bound+1):
            time = Real('time' + str(k))

            combineSub = self.combineDict(self.makeSubMode(k), self.makeSubVars(k, 't'))
            nextSub = self.combineDict(self.makeSubMode(k+1), self.makeSubVars(k+1, '0'))

            const = [i.substitution(combineSub) for i in jumpConsts]
            combineJump = [i.nextSub(nextSub) for i in const]
            result.append(Or(*combineJump))

        return And(*result)

    def flowConstraints(self, bound):
        result= list()
        for k in range(bound+1):
            time = Real('time' + str(k))
            flowConsts = list()
            for i in range(len(self.modeModule)):
                flowModule = dict()
                curMode = self.modeModule[i].getMode().getExpression(self.subvars)
                curFlow = self.modeModule[i].getFlow().getExpression() 
                for j in range(len(curFlow)):
                    if curFlow[j].getVarId() in self.subvars.keys():
                        flowModule[self.subvars[curFlow[j].getVarId()]] = curFlow[j].getFlow()
                    else:
                        raise ("Flow id is not declared")
                flowConsts.append(And(curMode.substitution(self.makeSubMode(k)), Integral(self.makeSubVars(k, 't'), self.makeSubVars(k, '0'), time, flowModule)))
            result.append(Or(*flowConsts))
        return And(*result)

    def invConstraints(self, bound):
        result = list()
        for k in range(bound+1):
            time = Real('time' + str(k))
            invConsts = list()
            for i in range(len(self.modeModule)):
                curMode = self.modeModule[i].getMode().getExpression(self.subvars)
                curInv = self.modeModule[i].getInv().getExpression(self.subvars)
                invConsts.append(curMode.substitution(self.makeSubMode(k)), Forall(time, curInv, self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k)))
            result.append(Or(*invConsts))
        return And(*result)

    # {propId : Expression} // {str :  Exp}
    def makePropDict(self):
        result = dict()
        for i in range(len(self.prop)):
            result[self.prop[i].getId()] = self.prop[i].getExpression(self.subvars)
        return result

    def propConstraints(self, propSet, bound):
        result = list()
        for k in range(bound+1):
            time = Real('time' + str(k))
            const = list()
            for i in self.makePropDict().keys():
                if str(i) in propSet:
                    for j in self.flow.keys():
                        const.append(Implies(And(i, j).substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[j]), time, self.prop[i], self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))))
                        const.append(Implies(And(Not(i), j).substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[j]), time, Not(self.prop[i]), self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))))
            result.append(And(*const))
        return And(*result)

    # Make constraints of the model
    def modelConstraints(self, bound, timeBound, partition, partitionConsts, formula):
        result = list()
        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))
        result.append(self.makeVarRangeConsts()) # make range constraint
        result.append(self.init.getExpression(self.subvars).substitution(combine)) # make initial constraint


        return result

    def reach(self):
        result = dict()
        for i in range(len(self.modeModule)):
#            print(self.modeModule[i].getMode().getExpression(self.subvars)) 
#            print(self.modeModule[i].getInv().getExpression(self.subvars))      
#            for j in range(len(self.modeModule[i].getFlow().getExpression())):
#                result[self.modeModule[i].getFlow().getExpression()[j].getVarId()] = self.modeModule[i].getFlow().getExpression()[j].getFlow()
            for j in range(len(self.modeModule[i].getJump().getRedeclList())):
                print(self.modeModule[i].getJump().getRedeclList()[j].getExpression(self.subvars))

        '''
        for i in range(len(self.modeVar)):
            print(self.modeVar[i])
        for i in range(len(self.contVar)):
            print(self.contVar[i])
        for i in range(len(self.modeModule)):
            print(self.modeModule[i]) 
        '''
        print("construct stlMC object") 
   

