import stlmcPy.core.encoding as ENC
from .node import *
from .differentiation import *

class modelConsts:
    def __init__(self, modeVar, contVar, varVal, modeModule, init, propositions, substitutionVars):
        self.modeVar = modeVar
        self.contVar = contVar
        self.varVal = varVal
        self.modeModule = modeModule
        self.init = init
        self.prop = propositions  # list type
        self.subvars = substitutionVars

    # Substitution proposition and mode variables according to bound k: {'fonepo' : fonepo_k}
    def makeSubMode(self, k):
        op = {'bool': Bool, 'int': Int, 'real': Real}
        result = {}
        for i in range(len(self.modeVar)):
            result[str(self.modeVar[i].id)] = op[self.modeVar[i].type](self.modeVar[i].id + '_' + str(k))
        return result

    def makeSubProps(self, k):
        result = {}
        for i in range(len(self.prop)):
            result[str(self.prop[i].getId())] = Bool(str(self.prop[i].getId()) + '_' + str(k))
        return result

    # Substituion varialbes according to bound k, sOe: var_k_0 or var_k_t
    def makeSubVars(self, k, sOe):
        op = {'bool': Bool, 'int': Int, 'real': Real}
        result = {}
        for i in range(len(self.contVar)):
            result[str(self.contVar[i].id)] = op[self.contVar[i].type](self.contVar[i].id + '_' + str(k) + '_' + sOe)
        return result

    # Make variable range constratint
    def makeVarRangeConsts(self, bound):
        result = list()
        for k in range(bound + 1):
            for i in range(len(self.contVar)):
                result.append(self.contVar[i].getConstraint().substitution(self.makeSubVars(k, '0')))
                result.append(self.contVar[i].getConstraint().substitution(self.makeSubVars(k, 't')))
        return And(*result)

    def combineDict(self, dict1, dict2):
        result = dict1.copy()
        for i in dict2.keys():
            result[i] = dict2[i]
        return result

    def jumpConstraints(self, bound):
        result = []
        for k in range(bound + 1):
            time = Real('time' + str(k))
            jumpConsts = list()
            combineSub = self.combineDict(self.makeSubMode(k), self.makeSubVars(k, 't'))
            combineSub.update(self.varVal)
            nextSub = self.combineDict(self.makeSubMode(k + 1), self.makeSubVars(k + 1, '0'))
            nextSub.update(self.varVal)

            for i in range(len(self.modeModule)):
                subresult = list()
                for j in range(len(self.modeModule[i].getJump().getRedeclList())):
                    subresult.append(self.modeModule[i].getJump().getRedeclList()[j].getExpression(self.subvars))
    
                # add steady state jump constraints
    
                steadyStateConsts = list()
                op = {'bool': Bool, 'int': Int, 'real': Real}
                for m in range(len(self.modeVar)):
                    mode = op[self.modeVar[m].type](self.modeVar[m].id)
                    steadyStateConsts.append(NextVar(mode) == mode)
                for m in range(len(self.contVar)):
                    var = op[self.contVar[m].type](self.contVar[m].id)
                    steadyStateConsts.append(NextVar(var) == var)
                subresult.append(And(*steadyStateConsts))
                
                modeConsts = list()
                for otherModeID in range(0, i):
                    modeConsts.append(Not(Real('currentMode_' + str(k)) == IntVal(otherModeID)))
                for otherModeID in range(i + 1, len(self.modeModule)):
                    modeConsts.append(Not(Real('currentMode_' + str(k)) == IntVal(otherModeID)))

                #                modeConsts.append(And(Real('currentMode_'+str(k)) >= RealVal(i), Real('currentMode_'+str(k)) <= RealVal(i)))

                modeConsts.append(Real('currentMode_' + str(k)) == IntVal(i))
                modeConsts.append(Real('currentMode_' + str(k)) < IntVal(len(self.modeModule)))
                modeConsts.append(Real('currentMode_' + str(k)) >= IntVal(0))


                jumpConsts.append(And(*[self.modeModule[i].getMode().getExpression(self.subvars), And(*modeConsts), Or(*subresult)]))

    
            const = [i.substitution(combineSub) for i in jumpConsts]
            combineJump = [i.nextSub(nextSub) for i in const]
            result.append(Or(*combineJump))

        return And(*result)

    def flowConstraints(self, bound):
        result = list()
        for k in range(bound + 1):
            time = Real('time' + str(k))
            flowConsts = list()
            for i in range(len(self.modeModule)):
                flowModule = dict()
                curMode = self.modeModule[i].getMode().getExpression(self.subvars)
                curFlow = self.modeModule[i].getFlow().getExpression(self.subvars)
                for j in range(len(curFlow)):
                    if curFlow[j].getVarId() in self.subvars.keys():
                        subdict = self.combineDict(self.subvars, self.makeSubMode(k))
                        subdict.update(self.varVal)
                        flowModule[self.subvars[curFlow[j].getVarId()]] = curFlow[j].getFlow(subdict)
                    else:
                        raise ("Flow id is not declared")
                                               
                flowConsts.append(Integral(curMode.substitution(self.makeSubMode(k)), self.makeSubVars(k, 't'), self.makeSubVars(k, '0'), time, flowModule,
                                               self.modeModule[i].getFlow().getFlowType()))

            result.append(Or(*flowConsts))
        return And(*result)

    # making key strID : matched atomic expression
    def makeAtomicDict(self, exp, startIndex, totalDict, bound):
        invAtomicID = "invAtomicID_"
        result = dict()
        copyList = list(exp.getListElem())
        for index in range(len(copyList)):
            element = copyList[index]
            if isinstance(element, And):
                returnResult = self.makeAtomicDict(element, len(totalDict), dict(), bound)[0]
                for subKey in returnResult.keys():
                    if not (subKey in totalDict.keys()):
                        totalDict[subKey] = invAtomicID + str(startIndex)
                        startIndex = startIndex + 1
                result.update(totalDict)
                formula = list()
                for strId in returnResult.keys():
                    formula.append(Bool(totalDict[strId] + "_" + str(bound)))
                copyList[index] = And(*formula)
            elif isinstance(element, Or):
                returnResult = self.makeAtomicDict(element, len(totalDict), dict(), bound)[0]
                for subKey in returnResult.keys():
                    if not (subKey in totalDict.keys()):
                        totalDict[subKey] = invAtomicID + str(startIndex)
                        startIndex = startIndex + 1

                result.update(totalDict)
                formula = list()
                for strId in returnResult.keys():
                    formula.append(Bool(totalDict[strId] + "_" + str(bound)))
                copyList[index] = Or(*formula)
            elif isinstance(element, Relational):
                if not (element in totalDict.keys()):
                    totalDict[element] = invAtomicID + str(startIndex)
                    startIndex = startIndex + 1
                result.update(totalDict)
                copyList[index] = Bool(totalDict[element] + "_" + str(bound))
            else:
                pass

        if len(copyList) > 1:
            returnFormula = {'and': And, 'or': Or}[exp.getOp().lower()](*copyList)
        elif len(copyList) == 1:
            returnFormula = copyList[0]
        else:
            returnFormula = BoolVal(True)

        return (result, returnFormula)

    def invConstraints(self, bound, delta):
        result = list()
        for k in range(bound + 1):
            combine = self.combineDict(self.makeSubMode(k), self.makeSubProps(k))
            combine.update(self.varVal)
            propIdDict = dict()
            invConsts = list()
            for i in range(len(self.modeModule)):
                subResult = list()
                curMode = self.modeModule[i].getMode().getExpression(self.subvars)
                curInv = self.modeModule[i].getInv().getExpression(self.subvars)
                (propIdDict, formula) = (self.makeAtomicDict(curInv, len(propIdDict), propIdDict, k))
                #invConsts.append(And(curMode, formula))
                curProp = list()
                if not isinstance(formula, Bool):
                    objct = formula.getListElem()
                    for o in objct:
                        curProp.extend([prop for prop, propId in propIdDict.items() if propId == str(o)[0:-2]])
                else:
                    curProp.extend([prop for prop, propId in propIdDict.items() if propId == str(formula)[0:-2]])

                curFlow = self.modeModule[i].getFlow()
                usingProp = dict()
                for cp in curProp:
                    usingProp[cp] = propIdDict[cp]
                for up in usingProp:
                    subResult.append(self.propForall(curMode.substitution(self.makeSubMode(k)), Bool(usingProp[up] + '_' + str(k)), up, k, curFlow, delta)) 
                invConsts.append(And(*subResult))
                # ex) {(> x1 0): 'invAtomicID_0', (> x2 0): 'invAtomicID_1', (< x2 50)}
                # Forall(curMode.substitution(self.makeSubMode(k)), formula, usingProp, k, curFlow) 
            result.append(Or(*invConsts))
        return And(*result)


    # {propId : Expression} // {str :  Exp}
    def makePropDict(self):
        result = dict()
        for i in range(len(self.prop)):
            result[self.prop[i].getId()] = self.prop[i].getExpression(self.subvars)
        return result

    def propInformula(self, formula):
        result = []
        if isinstance(formula, Leaf):
            if formula in self.makePropDict().keys():
                return [formula]
            else:
                return list()
        for i in list(formula.children):
            result.extend(self.propInformula(i))
        return result

    '''
    # For reachbility check, need to check!!!!
    def goalConstraints(self, bound, goal):
        result = list()
        for k in range(bound + 1):
            const = list()
            combine = self.combineDict(self.makeSubMode(k), self.makeSubProps(k))
            combine.update(self.varVal)
            const.append(goal.substitution(combine))

            for prop in propIdDict.keys():
                for m in range(len(self.modeModule)):
                    curMode = self.modeModule[m].getMode().getExpression(self.subvars)
                    curFlow = self.modeModule[m].getFlow()
                    const.append(Implies(curMode.substitution(self.makeSubMode(k)),
                                            self.propForall(self.makePropDict()[prop], k, curFlow)))
            result.append(And(*const))
        return Or(*result)
    '''

    def propForall(self, curMode, propID, exp, bound, curFlow, delta):

        combine = self.combineDict(self.makeSubMode(bound), self.makeSubProps(bound))
        combine.update(self.varVal)

        curFlowExp = curFlow.getExpression(self.subvars)
        curFlowType = curFlow.getFlowType()
        flowModule = dict()

        for j in range(len(curFlowExp)):
            if curFlowExp[j].getVarId() in self.subvars.keys():
                substitutionDict = self.combineDict(self.subvars, self.makeSubMode(bound))
                substitutionDict['time'] = Real('time' + str(bound))
                substitutionDict.update(self.varVal)
                flowModule[self.subvars[curFlowExp[j].getVarId()]] = curFlowExp[j].getFlow(substitutionDict)

            else:
                raise ("Flow id is not declared")

        if curFlowType == 'diff':
            for contVar in flowModule.keys():
                flowModule[contVar] = flowModule[contVar] * Real('time' + str(bound))
        subContVar = dict()
        for contVar in flowModule.keys():
            subContVar[str(contVar.id)] = flowModule[contVar]


        # Change proposition formula type to Gt or Ge
        if isinstance(exp, Lt):
            exp = Gt((exp.right() - exp.left()), RealVal(-1 * delta))
        elif isinstance(exp, Le):
            exp = Ge((exp.right() - exp.left()), RealVal(-1 * delta))
        elif isinstance(exp, Gt):
            exp = Gt(exp.left(), exp.right() - RealVal(delta))
        elif isinstance(exp, Ge):
            exp = Ge(exp.left(), exp.right() - RealVal(delta))

        initPointCond = exp.substitution(self.makeSubVars(bound, '0'))

        return And(initPointCond, Forall(curMode, propID, exp, combine, self.makeSubVars(bound, '0'), self.makeSubVars(bound, 't'), subContVar, delta))


    def propConstraints(self, propSet, bound, delta):
        result = list()
        for k in range(bound + 1):
            const = list()
            combine = self.combineDict(self.makeSubMode(k), self.makeSubProps(k))
            combine.update(self.varVal)
            for i in self.makePropDict().keys():
                if str(i) in propSet:
                    for m in range(len(self.modeModule)):
                        curMode = self.modeModule[m].getMode().getExpression(self.subvars)
                        curFlow = self.modeModule[m].getFlow()
                        #const.append(self.propForall(curMode.substitution(combine), i.substitution(combine), self.makePropDict()[i], k, curFlow))
                        const.append(Implies(And(i, curMode).substitution(combine),
                                             self.propForall(curMode.substitution(combine), i.substitution(combine), self.makePropDict()[i], k, curFlow, delta)))
                        #const.append(self.propForall(curMode.substitution(combine), Not(i).substitution(combine), Not(self.makePropDict()[i]).reduce(), k, curFlow))
                        const.append(Implies(And(Not(i), curMode).substitution(combine),
                                             self.propForall(curMode.substitution(combine), Not(i).substitution(combine), Not(self.makePropDict()[i]).reduce(), k, curFlow, delta)))

            result.append(And(*const))
        return And(*result)

    def timeBoundConsts(self, consts, timeBound):
        result = []
        variables = set().union(*[c.getVars() for c in consts])
        curMode = list()
        for i in range(len(self.modeModule)):
            curMode.append(self.modeModule[i].getMode().getExpression(self.subvars))
        for i in curMode:
            if i in variables:
                variables.remove(i)
        preVariables = list(variables)
        variables = sorted(preVariables, key=lambda x: str(x))
        for i in range(len(variables)):
            keyIndex = str(variables[i]).find('_')
            key = str(variables[i])[:keyIndex]
            if (key.find('time') != -1 or key.find('tau') != -1 or key.find('TauIndex') != -1):
                result.append(variables[i] >= RealVal(0))
                result.append(variables[i] <= RealVal(timeBound))
        return result

    # Make constraints of the model
    def modelConstraints(self, bound, timeBound, delta, partition, partitionConsts, formula):
        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))
        combine.update(self.varVal)
        # make range constraints
        rangeConsts = self.makeVarRangeConsts(bound)
        # make initial constraints
        initConst = self.init.getExpression(self.subvars).substitution(combine)
        # make invariant constraints
        invConsts = self.invConstraints(bound, delta)
        # make flow constraints
        flowConsts = self.flowConstraints(bound)
        # make jump constraints
        jumpConsts = self.jumpConstraints(bound)
        stlConsts = list()
        ts = [Real("tau_%s" % i) for i in range(0, bound + 2)]

        stlConsts.append(ts[0] >= RealVal(0))
        stlConsts.append(Real('time0') == ts[0])

        propSet = set()
        for f in partition.keys():
            if isinstance(f, ENC.PropositionFormula):
                propSet.add(str(f))

        '''
        for i in range(0, bound+1):
            stlConsts.append(Real('time' + str(i)) == (ts[i + 1] - ts[i]))
            stlConsts.append(ts[i] <= ts[i + 1])
        '''
        # time is duration
        for i in range(bound):
            stlConsts.append(Real('time' + str(i + 1)) == (ts[i + 1] - ts[i]))
            stlConsts.append(ts[i] <= ts[i + 1])

        stlConsts.append(self.propConstraints(propSet, bound, delta))

        addTimeBound = stlConsts + partitionConsts + formula

        stlConsts = stlConsts + self.timeBoundConsts(addTimeBound, timeBound)

        return ([rangeConsts, initConst, jumpConsts], invConsts, flowConsts, stlConsts)
