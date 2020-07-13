from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_expression
# TODO: why attribute error occured here?

class StlMC:
    def __init__(self, modeVar, contVar, varVal, modeModule, init, prop, formulaText):
        self.modeVar = modeVar
        self.contVar = contVar
        self.varVal = varVal
        self.modeModule = modeModule
        self.init = init
        self.prop = prop  # list type
        self.subvars = self.makeVariablesDict()
        # self.consts = modelConsts(self.modeVar, self.contVar, self.varVal, self.modeModule, self.init, self.prop,
        #                           self.subvars)

    def make_consts(self, bound, delta=None):
        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))
        combine.update(self.varVal)
        # make range constraints
        rangeConsts = self.makeVarRangeConsts(bound)
        # make initial constraints
        initConst = get_expression(self.init, self.subvars).substitution(combine)
        # make invariant constraints
        invConsts = self.invConstraints(bound, delta)
        # make flow constraints
        flowConsts = self.flowConstraints(bound)
        # make jump constraints
        jumpConsts = self.jumpConstraints(bound)

        return [rangeConsts, initConst, jumpConsts], invConsts, flowConsts

        # self.delta = delta
        # self.bound = bound
        # self.strStlFormula = str(stlFormula)
        # (constSize, fsSize) = (0, 0)
        # (stim1, etime1, stime2) = (0, 0, 0)
        # isUnknown = False
        # negFormula = NotFormula(stlFormula)  # negate the formula
        # isError = False
        #
        # solver2 = SolverFactory(solver).generate_solver()
        #
        # for i in range(0 if iterative else bound, bound + 1):
        #     stime1 = time.process_time()
        #
        #     baseP = PART.baseCase(i)
        #
        #     # generate (subformula, time index) map
        #     (partition, sepMap) = PART.guessPartition(negFormula, baseP)
        #
        #     # full separation
        #     fs = SEP.fullSeparation(negFormula, sepMap)
        #
        #     originalFS = dict()
        #     for (m, n) in fs[1].keys():
        #         originalFS[m] = fs[1][(m, n)]
        #
        #         # FOL translation
        #     baseV = ENC.baseEncoding(partition, baseP)
        #     (formulaConst, subFormulaMap) = ENC.valuation(fs[0], originalFS, ENC.Interval(True, 0.0, True, 0.0), baseV)
        #
        #     # partition constraints
        #     partitionConsts = PART.genPartition(baseP, fs[1], subFormulaMap)
        #
        #     # constraints from the model
        #     # (list, attribute, attribute, list)
        #     (transConsts, invConsts, flowConsts, stlConsts, timeConsts) = self.consts.modelConstraints(i, timeBound,
        #                                                                                                delta, partition,
        #                                                                                                partitionConsts,
        #                                                                                                [formulaConst])
        #     # modelConsts = []
        #     etime1 = time.process_time()
        #
        #     if onlySTL:
        #         print("only STL is true")
        #         allConsts = partitionConsts + [formulaConst]
        #     elif solver == 'hylaa':
        #         allConsts = [invConsts, formulaConst] + stlConsts + partitionConsts + transConsts
        #
        #         # allConsts = (partitionConsts + [formulaConst], stlConsts + [invConsts] + transConsts)
        #     else:
        #         allConsts = transConsts + [invConsts, flowConsts] + stlConsts + timeConsts + partitionConsts + [
        #             formulaConst]
        #         # allConsts = stlConsts + partitionConsts + [formulaConst]
        #         # allConsts = [invConsts]
        #
        #     (result, cSize, self.model) = solver2.solve(allConsts)
        #
        #     stime2 = time.process_time()
        #
        #     # calculate size
        #     fsSize += sum([ENC.size(f) for f in [fs[0]] + list(fs[1].values())])
        #     constSize += cSize
        #
        #     generationTime = round((etime1 - stime1), 4)
        #     solvingTime = round((stime2 - etime1), 4)
        #     totalTime = round((stime2 - stime1), 4)
        #
        # if isError:
        #     return (True, True, True, True, True, True)
        #
        # printResult(modelName, self.strStlFormula, str(result), bound, timeBound, constSize, fsSize,
        #             str(generationTime), str(solvingTime),
        #             str(totalTime))
        #
        # return (result, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime))

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
            result[str(self.contVar[i].id)] = op[self.contVar[i].type](
                self.contVar[i].id + '_' + str(k) + '_' + sOe)
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
                    subresult.append(get_expression(self.modeModule[i].getJump().getRedeclList()[j], self.subvars))

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

                jumpConsts.append(And(
                    *[get_expression(self.modeModule[i].getMode(), self.subvars), And(*modeConsts), Or(*subresult)]))

            const = [i.substitution(combineSub) for i in jumpConsts]
            combineJump = [i.nextSub(nextSub) for i in const]
            result.append(Or(*combineJump))

        return And(*result)

    def getFlow(self, diffeq: Dynamics, var_dict: dict):
        if type(diffeq.flow) in [RealVal, IntVal, BoolVal]:
            return diffeq.flow
        if type(diffeq.flow) in [Real, Int, Bool]:
            if str(diffeq.flow) in var_dict.keys():
                return var_dict[str(diffeq.flow)]
            else:
                return diffeq.flow
        return get_expression(diffeq.flow, var_dict)

    def flowConstraints(self, bound):
        result = list()
        for k in range(bound + 1):
            time = Real('time' + str(k))
            flowConsts = list()
            for i in range(len(self.modeModule)):
                flowModule = dict()
                curMode = get_expression(self.modeModule[i].getMode(), self.subvars)
                curFlow = get_expression(self.modeModule[i].getFlow(), self.subvars)
                for j in range(len(curFlow)):
                    if curFlow[j].getVarId() in self.subvars.keys():
                        subdict = self.combineDict(self.subvars, self.makeSubMode(k))
                        subdict.update(self.varVal)
                        flowModule[self.subvars[curFlow[j].getVarId()]] = self.getFlow(curFlow[j], subdict)
                    else:
                        raise ("Flow id is not declared")

                flowConsts.append(Integral(curMode.substitution(self.makeSubMode(k)), self.makeSubVars(k, 't'),
                                           self.makeSubVars(k, '0'), time, flowModule,
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
                curMode = get_expression(self.modeModule[i].getMode(), self.subvars)
                curInv = get_expression(self.modeModule[i].getInv(), self.subvars)
                (propIdDict, formula) = (self.makeAtomicDict(curInv, len(propIdDict), propIdDict, k))
                # invConsts.append(And(curMode, formula))
                curProp = list()
                if not isinstance(formula, Bool) and not isinstance(formula, Constant):
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
                    subResult.append(self.propForall(curMode.substitution(self.makeSubMode(k)),
                                                     Bool(usingProp[up] + '_' + str(k)), up, k, curFlow, delta))
                invConsts.append(And(*subResult))
                # ex) {(> x1 0): 'invAtomicID_0', (> x2 0): 'invAtomicID_1', (< x2 50)}
                # Forall(curMode.substitution(self.makeSubMode(k)), formula, usingProp, k, curFlow)
            result.append(Or(*invConsts))
        return And(*result)

    # {propId : Expression} // {str :  Exp}
    def makePropDict(self):
        result = dict()
        for i in range(len(self.prop)):
            result[self.prop[i].getId()] = get_expression(self.prop[i], self.subvars)
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


    @property
    def cont_id_dict(self):
        return self.__cont_id_dict

    @cont_id_dict.setter
    def cont_id_dict(self, id_dict_param):
        self.__cont_id_dict = id_dict_param

    # def getStlFormsList(self):
    #     return self.goal.getFormulas(self.subvars)

    # Transform the string id to Type(id) ex: 'a' -> Bool('a')
    def makeVariablesDict(self):
        op = {'bool': Bool, 'int': Int, 'real': Real}
        result = dict()
        for i in self.varVal.keys():
            result[str(i)] = self.varVal[i] + [invConsts]
        for i in range(len(self.modeVar)):
            result[str(self.modeVar[i].id)] = op[self.modeVar[i].type](self.modeVar[i].id)
        for i in range(len(self.contVar)):
            result[str(self.contVar[i].id)] = op[self.contVar[i].type](self.contVar[i].id)
        result['false'] = BoolVal(False)
        result['true'] = BoolVal(True)
        return result

    @property
    def data(self):
        result = dict()
        for i in self.varVal.keys():
            result[str(i)] = self.varVal[i]
        return (self.model, self.modeVar, self.contVar, result, self.prop, self.bound, self.modeModule,
                self.strStlFormula)

    # # an implementation of Algorithm 1 in the paper
    # def modelCheck(self, modelName, stlFormula, bound, timeBound, solver, logic, onlySTL, delta, goal: Goal, iterative=True):
    #     self.delta = delta
    #     self.bound = bound
    #     self.strStlFormula = str(stlFormula)
    #     (constSize, fsSize) = (0, 0)
    #     (stim1, etime1, stime2) = (0, 0, 0)
    #     isUnknown = False
    #     negFormula = NotFormula(stlFormula)  # negate the formula
    #     isError = False
    #     solver2 = SolverFactory(solver).generate_solver()
    #     goal.prepare(self.modeVar, self.contVar, self.varVal, self.modeModule, self.init, self.prop)
    #
    #     for i in range(0 if iterative else bound, bound + 1):
    #         stime1 = time.process_time()
    #
    #         baseP = PART.baseCase(i)
    #
    #         # generate (subformula, time index) map
    #         (partition, sepMap) = PART.guessPartition(negFormula, baseP)
    #
    #         # full separation
    #         fs = SEP.fullSeparation(negFormula, sepMap)
    #
    #         originalFS = dict()
    #         for (m, n) in fs[1].keys():
    #             originalFS[m] = fs[1][(m, n)]
    #
    #             # FOL translation
    #         baseV = ENC.baseEncoding(partition, baseP)
    #         (formulaConst, subFormulaMap) = ENC.valuation(fs[0], originalFS, ENC.Interval(True, 0.0, True, 0.0), baseV)
    #
    #         # partition constraints
    #         partitionConsts = PART.genPartition(baseP, fs[1], subFormulaMap)
    #
    #         # constraints from the model
    #         # (list, attribute, attribute, list)
    #         transConsts, invConsts, flowConsts = self.make_consts(i, delta)
    #         stlConsts, timeConsts = goal.make_consts(i, timeBound, delta, partition, formulaConst)
    #         # (transConsts, invConsts, flowConsts, stlConsts, timeConsts) = self.consts.modelConstraints(i, timeBound,
    #         #                                                                                            delta, partition,
    #         #                                                                                            partitionConsts,
    #         #                                                                                            [formulaConst])
    #         # modelConsts = []
    #         # stl proposition 에 대한 => //
    #         # partition ....?
    #
    #         etime1 = time.process_time()
    #
    #         if onlySTL:
    #             print("only STL is true")
    #             allConsts = partitionConsts + [formulaConst]
    #         elif solver == 'hylaa':
    #             allConsts = [invConsts, formulaConst] + stlConsts + partitionConsts + transConsts
    #
    #             # allConsts = (partitionConsts + [formulaConst], stlConsts + [invConsts] + transConsts)
    #         else:
    #             allConsts = transConsts + [invConsts, flowConsts] + stlConsts + timeConsts + partitionConsts + [
    #                 formulaConst]
    #             # allConsts = stlConsts + partitionConsts + [formulaConst]
    #             # allConsts = [invConsts]
    #
    #         (result, cSize, self.model) = solver2.solve(allConsts)
    #
    #         # check the satisfiability
    #         # if solver == 'z3':
    #         #     (result, cSize, self.model) = z3checkSat(allConsts, logic)
    #         # elif solver == 'yices':
    #         #     (result, cSize, self.model) = yicescheckSat(allConsts, logic)
    #
    #         stime2 = time.process_time()
    #
    #         # calculate size
    #         fsSize += sum([ENC.size(f) for f in [fs[0]] + list(fs[1].values())])
    #         constSize += cSize
    #
    #         generationTime = round((etime1 - stime1), 4)
    #         solvingTime = round((stime2 - etime1), 4)
    #         totalTime = round((stime2 - stime1), 4)
    #     if isError:
    #         return (True, True, True, True, True, True)
    #
    #     printResult(modelName, self.strStlFormula, str(result), bound, timeBound, constSize, fsSize,
    #                 str(generationTime), str(solvingTime),
    #                 str(totalTime))
    #
    #     return (result, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime))

    def reach(self, bound, timeBound, goal):
        self.bound = bound
        self.strStlFormula = str(goal)
        consts = []
        combine = self.consts.combineDict(self.consts.makeSubMode(0), self.consts.makeSubVars(0, '0'))
        consts.append(self.consts.makeVarRangeConsts(bound))
        consts.append(get_expression(self.init, self.subvars).substitution(combine))
        consts.append(self.consts.flowConstraints(bound))
        consts.append(self.consts.jumpConstraints(bound))
        consts.append(self.consts.goalConstraints(bound, goal))

        consts = consts + self.consts.timeBoundConsts(consts, timeBound)

        (result, cSize, self.model) = checkSat(consts)
        return result
