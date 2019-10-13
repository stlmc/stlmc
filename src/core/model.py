import core.partition as PART
import core.separation as SEP
import time
from .z3Handler import *
from .formula import *
from .z3Consts import *


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
    print(
                "Generation Time(sec) : " + generationTime + ", Solving Time(sec) : " + solvingTime + ", Total Time(sec) : " + totalTime + ".\n")
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

    def getExpression(self, varDict=dict()):
        return {'bool': Bool, 'int': Int, 'real': Real}[self.__type](self.__varId)


class Mode(Variable):
    def __init__(self, varType, varId):
        super().__init__(varType.lower(), varId)


class InitVal(Variable):
    def __init__(self, varId):
        self.__var_dic = dict()
        self.__value = 0.0
        self.__id = str(varId[0:-3])
        self.__var_dic[self.__id] = self.__value
        super().__init__("real", self.__id)

    def __repr__(self):
        return str(self.__id)

    # should call after dic is setted
    @property
    def value(self):
        self.__value = self.__var_dic[self.__id]
        return self.__value

    @value.setter
    def value(self, value):
        self.__value = value
        self.__var_dic[self.__id] = self.__value

    @property
    def var_dic(self):
        return self.__var_dic

    @var_dic.setter
    def var_dic(self, var_dic):
        self.__var_dic = var_dic

    def getType(self):
        return Type.Real

    def getInitValue(self, step):
        return Real(str(self.__varId) + "_" + str(step))

    def getVars(self):
        return self.getExpression().getVars()

    def substitution(self, subDict):
        return self.getExpression().substitution(subDict)


class ContVar(Variable):
    def __init__(self, interval, varId):
        super().__init__("real", varId)
        self.__varId = varId
        self.leftend = interval[0]
        self.left = interval[1]
        self.right = interval[2]
        self.rightend = interval[3]

    def __repr__(self):
        return super(ContVar, self).getVarString() + (' [' if self.leftend else ' (') + repr(self.left) + ',' + repr(
            self.right) + (']' if self.rightend else ')')

    def getConstraint(self):
        variable = {'bool': Bool, 'int': Int, 'real': Real}[self.type](self.__varId)
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
    def __init__(self, func, val, var_dict, init_dict):
        self.func = func
        self.val = val
        self._var_dict = var_dict
        self._init_dict = init_dict

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

    @property
    def value(self):
        if str(self.val) in self._var_dict.keys():
            degree = self._var_dict[str(self.val)]
        #elif str(self.val).isdigit():
        #    print("kekekek")
        #    degree = RealVal(float(self.val)).value
        # TODO: why need below? problems....
        #else:
        #    degree = Real(str(self.val)).value
        else:
            degree = RealVal(str(self.val)).value

        print("comeone")
        print(degree)

        if self.func == 'sin':
            return degree - degree * degree * degree / RealVal(6).value
        elif self.func == 'cos':
            return degree - degree * degree / RealVal(2).value
        elif self.func == 'tan':
            return degree + degree * degree * degree
        elif self.func == '-':
            return RealVal(0).value - degree
        else:
            raise "Not yet in Unary function"


class BinaryExp:
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right
        self._var_dict = dict()
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
        elif self.op == '**':
            return left ** right
        else:
            raise "Not yet in Binary Expression"

    def substitution(self, subDict):
        opdict = {'^': Pow, '+': Plus, '-': Minus, '*': Mul, '/': Div}
        return opdict[self.op](self.left().substitution(subDict), self.right().substitution(subDict))

    @property
    def var_dic(self):
        return self._var_dict

    @var_dic.setter
    def var_dic(self, var_dict):
        self._var_dict = var_dict

    @property
    def value(self):
        vleft = self.left
        vright = self.right
        vleft.var_dic = self._var_dict
        vright.var_dic = self._var_dict
        # TODO: Erase dependency
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
        # default is Bool Type
        self._type = Type.Bool
        self._left = left
        self._right = right

    def __repr__(self):
        return str(self._left) + " " + str(self.op) + " " + str(self._right)

    @property
    def left(self):
        return self._left

    @property
    def right(self):
        return self._right

    def getExpression(self, varDict):
        left = self._left
        right = self._right
        if isinstance(left, BinaryExp):
            left = left.getExpression(varDict)
        if isinstance(right, BinaryExp):
            right = right.getExpression(varDict)
        if str(self._left) in varDict.keys():
            left = varDict[str(self._left)]
        if str(self._right) in varDict.keys():
            right = varDict[str(self._right)]
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

    @property
    def type(self):
        return self._type


class Multy:
    def __init__(self, op, props):
        self.op = op.lower()
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
        return {'and': And, 'or': Or}[self.op](*result)


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
        return {'and': And, 'or': Or}[self.op](left, right)


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
        return {'not': Not, '~': Not}[self.op](prop)


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
        return {'not': Not, 'Not': Not, '~': Not}[self.op](prop)


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
        if type(self.flow) in [RealVal, IntVal, BoolVal]:
            return self.flow
        if type(self.flow) in [Real, Int, Bool] :
            if str(self.flow) in varDict.keys():
                return varDict[str(self.flow)]
            else:
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
    def __init__(self, contVar, flow):
        self.contVar = contVar
        self.flow = flow
        self.__ode = []

    def __repr__(self):
        return str(self.contVar) + " = " + str(self.flow)

    def getVarId(self):
        return str(self.contVar)

    def getSolStr(self):
        return str(self.flow)

    def getFlow(self, varDict):
        return self.flow.getExpression(varDict)

    def getExpression(self, varDict):
        result = dict()
        result[self.contVar] = self.flow.getExpression(varDict)
        return result

    def var2str(self):
        return str(self.contVar)

    @property
    def ode(self):
        self.__ode.append(self.flow.value)
        return self.__ode


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
        return (self.flow)

    # return jumpDecl type
    def getJump(self):
        return (self.jump)


class flowDecl:
    def __init__(self, expType, exps, var_dict):
        self.type = expType  # empty : wrong, diff : diff_eq(), sol : sol_eq()
        self.exps = exps
        self.__var_dict = var_dict
        print(exps)

    @property
    def var_dict(self):
        return self.__var_dict

    def __repr__(self):
        return str(self.type) + " " + str(self.exps)

    def getFlowType(self):
        return self.type

    def exp(self):
        return self.exps

    def getExpression(self, varDict):
        return self.exps

    def exp2exp(self):

        ode_list = []
        print("comeon")
        print(self.__var_dict)
        print(self.exps)
        for elem in self.exps:
            # for e in elem.flow:
            if isinstance(elem.flow, RealVal):
#                 print("realval")
#                 print(elem)
                ode_list.append(elem.flow.value)
            elif isinstance(elem.flow, Real):
#                 print("real")
#                 print(elem)
                ode_list.append(elem.flow.value)
                # every thing goes in here
            else:
#                 print("else")
#                 print(type(elem.flow))
                # elem.flow is BinaryExp type
                elem.flow.var_dic = self.__var_dict
#                 print("inside")
#                 print(elem.flow)
#                 print(elem.flow.var_dic)
#                 print(elem.flow.value)
#                 print("````````inside")
                ode_list.append(elem.flow.value)
        #print("return")
        #print(ode_list)
        return ode_list

    @property
    def ode(self):
        self.__ode.append(self.flow.value)
        return self.__ode


class jumpRedeclModule:
    def __init__(self, cond, jumpRedecl):
        self.cond = cond
        self.jumpRedecl = jumpRedecl

    def __repr__(self):
        return str(self.cond) + " " + str(self.jumpRedecl)

    def getCond(self, varDict):
        condition = self.cond.getExpression(varDict)
        return condition

    def getExpression(self, varDict):
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
            if isinstance(self.exp, Constant):
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
        self.prop = prop  # list type
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
        op = {'bool': Bool, 'int': Int, 'real': Real}
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
        return (self.model, self.modeVar, self.contVar, self.subvars, self.prop, self.bound, self.modeModule,
                self.strStlFormula)

    # an implementation of Algorithm 1 in the paper
    def modelCheck(self, stlFormula, bound, timeBound, iterative=True):
        self.bound = bound
        self.strStlFormula = str(stlFormula)
        (constSize, fsSize) = (0, 0)
        (stim1, etime1, stime2) = (0, 0, 0)
        isUnknown = False
        negFormula = NotFormula(stlFormula)  # negate the formula

        print("Scheduleing " + str(stlFormula) + " bound: " + str(bound))

        for i in range(0 if iterative else bound, bound + 1):

            stime1 = time.process_time()
            # base partition
            baseP = PART.baseCase(i)

            # partition constraint
            (partition, sepMap, partitionConsts) = PART.guessPartition(negFormula, baseP)
            '''
            print("partition")
            print(partition)
            print("sepMap")
            print(sepMap)
            '''
            # full separation
            fs = SEP.fullSeparation(negFormula, sepMap)
            # FOL translation
            '''
            print("full separation result formula")
            print(str(fs[0]))
            print("full separtion map")
            print(fs[1])
            '''
            baseV = ENC.baseEncoding(partition, baseP)
            '''
            print("baseV")
            print(baseV)
            '''
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
            fsSize += sum([ENC.size(f) for f in [fs[0]] + list(fs[1].values())])
            constSize += cSize

            generationTime = round((etime1 - stime1), 4)
            solvingTime = round((stime2 - etime1), 4)
            totalTime = round((stime2 - stime1), 4)

            if result == z3.sat:
                printResult("False", i, timeBound, constSize, fsSize, str(generationTime), str(solvingTime),
                            str(totalTime))
                return (False, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime))  # counterexample found
            if result == z3.unknown:
                isUnknown = True

        result = "Unknown" if isUnknown else True
        printResult(str(result), bound, timeBound, constSize, fsSize, str(generationTime), str(solvingTime),
                    str(totalTime))

        return (result, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime))





    def reach(self, bound, timeBound, goal):
        self.bound = bound
        self.strStlFormula = str(goal)
        consts = []
        combine = self.consts.combineDict(self.consts.makeSubMode(0), self.consts.makeSubVars(0, '0'))
        consts.append(self.consts.makeVarRangeConsts(bound))
        consts.append(self.init.getExpression(self.subvars).substitution(combine))
        consts.append(self.consts.flowConstraints(bound))
        consts.append(self.consts.jumpConstraints(bound))
        consts.append(self.consts.goalConstraints(bound, goal))
      

        consts = consts + self.consts.z3TimeBoundConsts(consts, timeBound)

        #        consts.append(goal.substitution(self.combineDict(self.makeSubMode(bound), self.makeSubVars(bound, 't'))))
        (result, cSize, self.model) = checkSat(consts)
        print(result)
        return result
