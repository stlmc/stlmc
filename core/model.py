import core.partition as PART
import core.separation as SEP
from .formula import *
from .z3Consts import *
import time
from .z3Handler import checkSat

def isNumber(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

def printResult(result, k, tauMax, cSize, fSize, generationTime, solvingTime, totalTime):
    print(result + " at bound k : " + str(k) + ", time bound : " + str(tauMax) + ".")
    print("Constraint Size : " + str(cSize) + ", Translation Size : " + str(fSize) + ".")
    print("Generation Time(sec) : " + generationTime + ", Solving Time(sec) : " + solvingTime + ", Total Time(sec) : " + totalTime + ".\n")
    print("--------------------------------------------------------------------------------------\n")


class Variable:
     def __init__(self, varType, varId):
         self.type = varType
         self.varId = varId
     def __repr__(self):
         return str(self.type) + " " + str(self.varId)
     def getVarString(self):
         return str(self.type) + " " + str(self.varId)
     def getType(self):
         return str(self.type)
     def getId(self):
         return str(self.varId)
     def getExpression(self):
         return {'bool' : Bool, 'int' : Int, 'real' : Real}[self.type](self.varId)

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
         if isinstance(left, BinaryExp):
             left = left.getExpression(varDict)
         if isinstance(right, BinaryExp):
             right = right.getExpression(varDict)
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
         if isinstance(left, BinaryExp):
             left = left.getExpression(varDict)
         if isinstance(right, BinaryExp):
             right = right.getExpression(varDict)
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

class Binary:
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right
    def __repr__(self):
        return "(" + str(self.op) + " " + str(self.left) + " " + str(self.right) + ")"
    def getExpression(self, varDict):
        left = self.left.getExpression(varDict)
        right = self.right.getExpression(varDict)
        return {'and' : And, 'or' : Or}[self.op](left, right)

class Unary:
    def __init__(self, op, prop):
        self.op = op
        self.prop = prop
    def __repr__(self):
        return str(self.op) + " " + repr(self.prop)
    def getExpression(self, varDict):
        if self.prop in varDict.keys():
            prop = varDict[self.prop]
        else: 
            raise("Proposition is not declared in unary class")
        return {'not' : Not}[self.op](prop)

class MultyCond(Multy):
    pass

class BinaryCond(Binary):
    pass

class UnaryCond(Unary):
    pass

class MultyJump(Multy):
    pass

class BinaryJump(Binary):
    pass

class UnaryJump(Unary):
    def getExpression(self, varDict):
        if isinstance(self.prop, NextVar):
            prop = self.prop
        else:
            prop = self.prop.getExpression(varDict)
        return {'not' : Not}[self.op](prop)

class DiffEq:
    def __init__(self, contVar, flow):
        self.contVar = contVar
        self.flow = flow
    def __repr__(self):
        return str(self.contVar) + " = " + str(self.flow)
    def getVarId(self):
        return str(self.contVar)
    def getFlow(self, varDict):
        if type(self.flow) in [RealVal, IntVal, BoolVal]:
            return self.flow
        return self.flow.getExpression(varDict)
    def getExpression(self, varDict):
        result = dict()
        result[self.contVar] = self.flow.getExpression(varDict)
        return result

class SolEq:
    def __init__(self, contVar, Sol):
        self.contVar = contVar
        self.sol = Sol
    def __repr__(self):
        return str(self.contVar) + " = " + str(self.sol)
    def getVarId(self):
        return str(self.contVar)
    def getFlow(self, varDict):
        if isinstance(self.sol, str):
            return self.sol           
        return self.sol.getExpression(varDict)
    def getExpression(self, varDict):
        result = dict()
        resutl[self.contVar] = self.sol.getExpression(varDict)
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
    def getExpression(self, varDict):
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
    def getType(self):
        return Type.Bool

class formulaDecl:
    def __init__(self, formulaList):
        self.formulaList = formulaList  # string type formulas
    def getFormulas(self, propDict):
        return self.formulaList
    def getNumOfForms(self):
        return len(self.formulaList)

class StlMC:
    def __init__(self, modeVar, contVar, modeModule, init, prop, goal, formulaText):
        self.modeVar = modeVar
        self.contVar = contVar
        self.modeModule = modeModule
        self.init = init
        self.prop = prop    #list type
        self.goal = goal
        self.subvars = self.makeVariablesDict()
        self.consts = z3Consts(self.modeVar, self.contVar, self.modeModule, self.init, self.prop, self.subvars)
        self.formulaText = formulaText

    def getStlFormsList(self):
        return self.goal.getFormulas(self.subvars)

    def getStlFormsText(self):
        return self.formulaText

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

   # an implementation of Algorithm 1 in the paper
    def modelCheck(self, stlFormula, bound, timeBound, iterative=True):
        (constSize, fsSize) = (0, 0)
        (stim1, etime1, stime2) = (0, 0, 0)
        isUnknown = False
        negFormula = NotFormula(stlFormula)  # negate the formula

        for i in range(0 if iterative else bound, bound + 1):

            stime1 = time.process_time()
            # base partition
            baseP = PART.baseCase(i)

            # partition constraint
            (partition,sepMap,partitionConsts) = PART.guessPartition(negFormula, baseP)
            
            # full separation
            fs = SEP.fullSeparation(negFormula, sepMap)

            # FOL translation
            baseV = ENC.baseEncoding(partition,baseP)
            formulaConst = ENC.valuation(fs[0], fs[1], ENC.Interval(True, 0.0, True, 0.0), baseV)

            # constraints from the model
            modelConsts = self.consts.modelConstraints(i, timeBound, partition, partitionConsts, [formulaConst])

            #for i in range(len(modelConsts)):
            #    print(modelConsts[i])

            etime1 = time.process_time()

            # check the satisfiability
            (result, cSize) = checkSat(modelConsts + partitionConsts + [formulaConst])

            stime2 = time.process_time()

            # calculate size
            fsSize += sum([ENC.size(f) for f in [fs[0]]+list(fs[1].values())])
            constSize += cSize

            generationTime = round((etime1-stime1),4)
            solvingTime = round((stime2-etime1), 4)
            totalTime = round((stime2-stime1), 4)

            if  result == z3.sat:
                printResult("False", i, timeBound, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime))
                return (False, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime))  # counterexample found
            if  result == z3.unknown:
                isUnknown = True

        result = "Unknown" if isUnknown else True
        printResult(str(result), bound, timeBound, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime))

        return (result, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime)) 


    def reach(self, bound, goal):
        consts = []
        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))
        consts.append(self.init.getExpression(self.subvars).substitution(combine))
        consts.append(self.consts.flowConstraints(bound))
#        consts.append(goal.substitution(self.combineDict(self.makeSubMode(bound), self.makeSubVars(bound, 't'))))
        return checkSat(consts)
