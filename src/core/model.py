import core.partition as PART
import core.separation as SEP
from .formula import *
from .z3Consts import *
import time

def flatten(l):
    res = []
    if isinstance(l, list):
        for elem in l:
            if isinstance(elem, list):
                for elemofelem in elem:
                    res.append(elemofelem)
            else:
                res.append(elem)
    else:
        res.append(l)
    return res

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
         self.__type = varType
         self.__varId = varId
     
     def __repr__(self):
         return str(self.__type) + " " + str(self.__varId)
     
     @property
     def type(self):
         return str(self.__type)

     @type.setter
     def type(self, type):
         self.__type = type
     
     @property
     def id(self):
         return str(self.__varId)

     @id.setter
     def id(self, id):
         self.__varId = id
     
     def getExpression(self):
         return {'bool' : Bool, 'int' : Int, 'real' : Real}[self.__type](self.__varId)

class Mode(Variable):
     def __init__(self, varType, varId):
         super().__init__(varType, varId)
         
class ContVar(Variable):
     def __init__(self, interval, varId):
         super().__init__("real", varId)
         self.__varId = varId
         self.leftend = interval[0]
         self.left = interval[1]
         self.right = interval[2]
         self.rightend = interval[3]
     def __repr__(self):
         return super(ContVar,self).getVarString() + (' [' if self.leftend else ' (') + repr(self.left) + ',' + repr(self.right) + (']' if self.rightend else ')')
     def getConstraint(self):
         variable =  {'bool' : Bool, 'int' : Int, 'real' : Real}[self.type](self.__varId)
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

class UnaryFunc:
     def __init__(self, func, val):
         self.func = func
         self.val = val

     def __repr__(self):
         return str(self.func) + "(" + str(self.val) + ")"

     def getExpression(self, varDict):
         if str(self.val) in varDict.keys():
             degree = varDict[str(self.val)]  
         elif str(self.val).isdigit():
             degree = RealVal(float(self.val))
         else:
             degree = Real(str(self.val))
         if self.func == 'sin':
             return degree - degree * degree * degree / RealVal(6)
         elif self.func == 'cos':
             return degree - degree * degree / RealVal(2)
         elif self.func == 'tan':
             return degree + degree * degree * degree
         elif self.func == '-':
             return RealVal(0) - degree
         else:
             raise "Not yet in Unary function"

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
        if isinstance(left, BinaryExp) or isinstance(left, UnaryFunc):
            left = left.getExpression(varDict)
        if isinstance(right, BinaryExp) or isinstance(right, UnaryFunc):
            right = right.getExpression(varDict)
        if str(self.left) in varDict.keys(): 
            left = varDict[str(self.left)]
        if str(self.right) in varDict.keys():
           right = varDict[str(self.right)]
        else:
            pass

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
    def substitution(self, subDict):
        opdict = {'^': Pow, '+': Plus, '-': Minus, '*': Mul, '/': Div}
        return opdict[self.op](self.left().substitution(subDict), self.right().substitution(subDict))
    
    @property
    def value(self):
        vleft = self.left
        vright = self.right
        if isinstance(self.left, BinaryExp):
            left = self.left.value
        if isinstance(self.right, BinaryExp):
            right = self.right.value
        if self.op == '+':
            return vleft.value + vright.value
        if self.op == '-':
            return vleft.value - vright.value
        if self.op == '*':
            return vleft.value * vright.value
        if self.op == '/':
            return vleft.value / vright.value

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
        return str(self.left) + " " + str(self.op) + " " + str(self.right)
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
            if isinstance(self.props[i], NextVar):
                exp = self.props[i]
            elif self.props[i] in varDict.keys():
                exp = varDict[self.props[i]]
            else:
                exp = self.props[i].getExpression(varDict)
            result.append(exp)
        return {'and' : And, 'or' : Or}[self.op](*result)

class Binary:
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right
    def __repr__(self):
        return "(" + str(self.op) + " " + str(self.left) + " " + str(self.right) + ")"
    def getExpression(self, varDict):
        if str(self.left) in varDict.keys():
            left = varDict[str(self.left)]
        else:
            left = self.left.getExpression(varDict)
        
        if str(self.right) in varDict.keys():
            right = varDict[str(self.right)]
        else:
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
            prop = self.prop.getExpression(varDict)           
        return {'not' : Not, '~' : Not}[self.op](prop)

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
        self.__ode = []

    @property
    def var_dic(self):
        return self.__var_dic

    @var_dic.setter
    def var_dic(self, vdic):
        self.__var_dic = vdic

    def __repr__(self):
        return str(self.contVar) + " = " + str(self.flow)
   
    def var2str(self):
        return str(self.contVar)

    def getVarId(self):
        return str(self.contVar)
    
    def getFlow(self, varDict):
        if type(self.flow) in [RealVal, IntVal, BoolVal, Real]:
            return self.flow
        return self.flow.getExpression(varDict)
    
    def getExpression(self, varDict):
        result = dict()
        result[self.contVar] = self.flow.getExpression(varDict)
        return result
    
    @property
    def ode(self):
        self.__ode.append(self.flow.value)
        return self.__ode


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
    def __init__(self, expType, exps, var_dict):
        self.type = expType   # empty : wrong, diff : diff_eq(), sol : sol_eq()
        self.exps = exps
        self.__var_dict = var_dict
        #for e in self.exps:
        #    varlist.append(e.contVar)
        #self.__cont_id_dict = dict()
        #for i in range(len(varlist)):
        #    self.__cont_id_dict[Real(varlist[i])]=0.0
   
    @property
    def var_dict(self):
        return self.__var_dict


    def __repr__(self):
        return str(self.type) + " " +  str(self.exps)
    
    def exp(self):
        return self.exps

    def getExpression(self, varDict):
        return self.exps
    
    def exp2exp(self):
        ode_list = []
        for elem in self.exps:
            #elem.var_dic = self.__cont_id_dict
            ode_inner_list = []
            #for e in elem.flow:
            if isinstance(elem.flow, RealVal):
                ode_list.append(elem.flow.value)
            elif isinstance(elem.flow, Real):
                ode_list.append(elem.flow.value)
                # every thing goes in here
            else:
                ode_list.append(elem.flow.value)
        return ode_list 

 
class jumpRedeclModule:
    def __init__(self, cond, jumpRedecl):
        self.cond = cond
        self.jumpRedecl =jumpRedecl
    def __repr__(self):
        return str(self.cond) + " " + str(self.jumpRedecl)
    def getCond(self, varDict):
        condition = self.cond.getExpression(varDict)
        return condition
    def getExpression(self,varDict):
        condition = self.cond.getExpression(varDict)
        redecl = self.jumpRedecl.getExpression(varDict)
        return And(condition, redecl)
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
              elif isinstance(self.exp, Real):
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
        if self.cond in varDict.keys():
            return varDict[self.cond]
        return self.cond.getExpression(varDict)
    def getId(self):
        return Bool(str(self.id))
    def getType(self):
        return Type.Bool
    def getExpStr(self):
        return str(self.cond)

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
        
    @property
    def cont_id_dict(self):
        return self.__cont_id_dict
    
    @cont_id_dict.setter
    def cont_id_dict(self, id_dict_param):
        self.__cont_id_dict = id_dict_param


    def getStlFormsList(self):
        return self.goal.getFormulas(self.subvars)

    # Transform the string id to Type(id) ex: 'a' -> Bool('a')
    def makeVariablesDict(self):
        op = {'bool' : Bool, 'int' : Int, 'real' : Real}
        result = dict()
        for i in range(len(self.modeVar)):
            result[str(self.modeVar[i].id)] = op[self.modeVar[i].type](self.modeVar[i].id)
        for i in range(len(self.contVar)):
            result[str(self.contVar[i].id)] = op[self.contVar[i].type](self.contVar[i].id)
        result['false'] = BoolVal(False)
        result['true'] = BoolVal(True)
        return result

    @property
    def data(self):
        return (self.model, self.modeVar, self.contVar, self.subvars, self.prop, self.bound, self.modeModule, self.strStlFormula)

   # an implementation of Algorithm 1 in the paper
    def modelCheck(self, stlFormula, bound, timeBound, iterative=True):
        self.bound = bound
        self.strStlFormula = str(stlFormula)
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

            '''
            for i in range(len(modelConsts)):
                print(modelConsts[i])
            '''

            etime1 = time.process_time()

            # check the satisfiability
            (result, cSize, self.model) = checkSat(modelConsts + partitionConsts + [formulaConst])

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
