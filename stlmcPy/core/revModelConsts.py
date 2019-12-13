import core.encoding as ENC
from .node import *
from .differentiation import *

class modelConsts:
    def __init__(self, modeVar, contVar, varVal, modeModule, init, propositions, substitutionVars):
        self.modeVar = modeVar
        self.contVar = contVar
        self.varVal = varVal
        self.modeModule = modeModule
        self.init = init
        self.prop = propositions    #list type
        self.subvars = substitutionVars


    # Substitution proposition and mode variables according to bound k: {'fonepo' : fonepo_k}
    def makeSubMode(self, k):
        op = {'bool' : Bool, 'int' : Int, 'real' : Real}
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
        op = {'bool' : Bool, 'int' : Int, 'real' : Real}
        result = {}
        for i in range(len(self.contVar)):
            result[str(self.contVar[i].id)] = op[self.contVar[i].type](self.contVar[i].id + '_' + str(k) + '_' + sOe)
        return result

    # Make variable range constratint
    def makeVarRangeConsts(self, bound):
        result = list()
        for k in range(bound+1):
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
        jumpConsts = list()
        for i in range(len(self.modeModule)):
            subresult = list()
            for j in range(len(self.modeModule[i].getJump().getRedeclList())):
                subresult.append(self.modeModule[i].getJump().getRedeclList()[j].getExpression(self.subvars))

            # add steady state jump constraints
            
            steadyStateConsts = list()
            op = {'bool' : Bool, 'int' : Int, 'real' : Real}
            for k in range(len(self.modeVar)):
                mode = op[self.modeVar[k].type](self.modeVar[k].id)
                steadyStateConsts.append(NextVar(mode) == mode)
            for k in range(len(self.contVar)):
                var = op[self.contVar[k].type](self.contVar[k].id)
                steadyStateConsts.append(NextVar(var) == var)
            subresult.append(And(*steadyStateConsts))
           

            jumpConsts.append(And(self.modeModule[i].getMode().getExpression(self.subvars), Or(*subresult)))

        result = []
        for k in range(bound+1):
            time = Real('time' + str(k))

            combineSub = self.combineDict(self.makeSubMode(k), self.makeSubVars(k, 't'))
            combineSub.update(self.varVal)
            nextSub = self.combineDict(self.makeSubMode(k+1), self.makeSubVars(k+1, '0'))
            nextSub.update(self.varVal)

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
                flowType = self.modeModule[i].getFlow().getFlowType()
                time = Real('time' + str(k)) if flowType == 'diff' else Real('tau_' + str(k))
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
                modeConsts = list()
                
                for otherModeID in range(0, i):
                    modeConsts.append(Not(Real('currentMode_'+str(k)) == IntVal(otherModeID)))
                for otherModeID in range(i+1, len(self.modeModule)):
                    modeConsts.append(Not(Real('currentMode_'+str(k)) == IntVal(otherModeID)))

#                modeConsts.append(And(Real('currentMode_'+str(k)) >= RealVal(i), Real('currentMode_'+str(k)) <= RealVal(i)))

                modeConsts.append(Real('currentMode_'+str(k)) == IntVal(i))
                modeConsts.append(Real('currentMode_'+str(k)) < IntVal(len(self.modeModule)))
                modeConsts.append(Real('currentMode_'+str(k)) >= IntVal(0))
               

                modeConsts.append(And(curMode.substitution(self.makeSubMode(k)), Integral(self.makeSubVars(k, 't'), self.makeSubVars(k, '0'), time, flowModule,flowType))) 
                flowConsts.append(And(*modeConsts))
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
                returnResult = self.makeAtomicDict(element, len(result), dict(), bound)[0]
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
                returnResult = self.makeAtomicDict(element, len(result), dict(), bound)[0]
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

        returnFormula = {'and' : And, 'or' : Or}[exp.getOp().lower()](*copyList) if (len(copyList) > 1) else (copyList[0] if (len(copyList) == 1) else BoolVal(True))

        return (result, returnFormula) 

    def invConstraints(self, bound):
       result = list()
       atomicDict = dict()
       for i in range(len(self.modeModule)): 
           curMode = self.modeModule[i].getMode().getExpression(self.subvars)
           curInv = self.modeModule[i].getInv().getExpression(self.subvars)
           invConsts = list()
           propIdDict = dict()
           for k in range(bound+1):
               time = Real('time' + str(k))
               (propIdDict, formula) = (self.makeAtomicDict(curInv, len(atomicDict), propIdDict, k))
               atomicDict.update(propIdDict)
               invConsts.append(formula)
           curFlow = self.modeModule[i].getFlow()
           for prop in propIdDict.keys():
               for k in range(bound+1):
                   invConsts.append(Bool(propIdDict[prop] + "_" + str(k)) == self.propForall(prop, k, curFlow))
           result.append(And(*invConsts))
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


    def goalConstraints(self, bound, goal):
        result = list()
        for k in range(bound+1):
            const = list()
            combine = self.combineDict(self.makeSubMode(k), self.makeSubProps(k))
            combine.update(self.varVal)
            const.append(goal.substitution(combine))
            for prop in self.propInformula(goal):
                time = Real('time' + str(k))
                const.append(self.makeSubProps(k)[str(prop)] == Forall(time, self.makePropDict()[prop], self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k)))
                const.append(Not(self.makeSubProps(k)[str(prop)]) == Forall(time, Not(self.makePropDict()[prop]), self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k)))
            result.append(And(*const))
        return Or(*result)

    def propForall(self, exp, bound, curFlow):
        # Change proposition formula type to Gt or Ge
        if isinstance(exp, Lt):
            exp = Gt((exp.right() - exp.left()), RealVal(0))
        if isinstance(exp, Le):
            exp = Ge((exp.right() - exp.left()), RealVal(0))

        # If proposition is just boolean variable, return original expression
        if not (isinstance(exp, Gt) or isinstance(exp, Ge)):
            if exp.getType() == Type.Bool:
                return exp.substitution(self.makeSubMode(bound))
            else:
                print(exp)
                print(exp.getType())
                raise ("Proposition constraints something wrong")

        # Case Real value >(or >=) 0
        if len(exp.getVars()) == 0 :
            return exp

        const = list()
        combine = self.combineDict(self.makeSubMode(bound), self.makeSubProps(bound))
        combine.update(self.varVal)
        handlingExp = exp.left() - exp.right()

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
        substitutionExp = handlingExp.substitution(subContVar)
        diffExp = diff(substitutionExp)

        #monotone increase or decrease
        const.append(Or(Ge(diffExp,RealVal(0)), Le(diffExp,RealVal(0))))

        # Special case : a == b
        if isinstance(exp, Numeq):
            subconst = list()
            subconst.append(Numeq(handlingExp.substitution(self.makeSubVars(bound,'0')), RealVal(0)))
            subconst.append(Numeq(handlingExp.substitution(self.makeSubVars(bound,'t')), RealVal(0)))
            subconst.append(Numeq(diffExp, RealVal(0)))
            return subconst

        # Special case : a =/= b
        if isinstance(exp, Numneq):
            subconst = list()
            subconst.append(self.propForall(Gt(handlingExp, RealVal(0)), bound, curFlow))
            subconst.append(self.propForall(Lt(handlingExp, RealVal(0)), bound, curFlow))
            return Or(*subconst)

        # f(t') >= 0
        const.append(Ge(handlingExp.substitution(self.makeSubVars(bound,'t')), RealVal(0)))

        if isinstance(exp, Gt):
            # Check a start point of interval satisfies the proposition
            const.append(Gt(handlingExp.substitution(self.makeSubVars(bound,'0')), RealVal(0)))
            # Case : f(t) = 0 -> dot(f(T)) > 0, forall T in (t, t')
            const.append(Implies(handlingExp.substitution(self.makeSubVars(bound,'0')) == RealVal(0), self.propForall(Gt(diffExp,RealVal(0)), bound, curFlow)))
            # Case : f(t') = 0 -> dot(f(T)) < 0, forall T in (t, t')
            const.append(Implies(handlingExp.substitution(self.makeSubVars(bound,'t')) == RealVal(0), self.propForall(Lt(diffExp, RealVal(0)), bound, curFlow)))
        elif isinstance(exp,Ge):
            const.append(Ge(handlingExp.substitution(self.makeSubVars(bound,'0')), RealVal(0)))
            const.append(Implies(handlingExp.substitution(self.makeSubVars(bound,'0')) == RealVal(0), self.propForall(Ge(diffExp,RealVal(0)), bound, curFlow)))
            const.append(Implies(handlingExp.substitution(self.makeSubVars(bound,'t')) == RealVal(0), self.propForall(Le(diffExp, RealVal(0)), bound, curFlow)))
        else:
            raise ("proposition constraint case mismatched")

        return And(*const)


    def propConstraints(self, propSet, bound):
        result = list()
        for k in range(bound+1):
            const = list()
            combine = self.combineDict(self.makeSubMode(k), self.makeSubProps(k))
            combine.update(self.varVal)
            for i in self.makePropDict().keys():
                if str(i) in propSet:
                    for m in range(len(self.modeModule)):
                        curMode = self.modeModule[m].getMode().getExpression(self.subvars)
                        curFlow = self.modeModule[m].getFlow()
                        const.append(Implies(And(i, curMode).substitution(combine), self.propForall(self.makePropDict()[i], k, curFlow)))
                        const.append(Implies(And(Not(i), curMode).substitution(combine), self.propForall(Not(self.makePropDict()[i]).reduce(), k, curFlow)))
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
        variables = sorted(preVariables, key = lambda x : str(x))
        for i in range(len(variables)):
            keyIndex = str(variables[i]).find('_')
            key = str(variables[i])[:keyIndex]
            if (key.find('time') != -1 or key.find('tau') != -1 or key.find('TauIndex') != -1): 
                result.append(variables[i] > RealVal(0))
                result.append(variables[i] <= RealVal(timeBound))
        return result

    # Make constraints of the model
    def modelConstraints(self, bound, timeBound, partition, partitionConsts, formula):
        result = list()
        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))
        combine.update(self.varVal)
        # make range constraints
        result.append(self.makeVarRangeConsts(bound))
        # make initial constraints
        result.append(self.init.getExpression(self.subvars).substitution(combine))
        # make invariant constraints
        result.append(self.invConstraints(bound))
        # make flow constraints
        result.append(self.flowConstraints(bound))
        # make jump constraints
        result.append(self.jumpConstraints(bound))

        ts = [Real("tau_%s"%i) for i in range(0, bound+1)]

        result.append(ts[0] >= RealVal(0))
        result.append(Real('time0') == ts[0])

        propSet = set()
        for f in partition.keys():
            if isinstance(f, ENC.PropositionFormula):
               propSet.add(str(f))

        for i in range(bound):
            result.append(Real('time' + str(i+1)) == (ts[i+1] - ts[i]))
            result.append(ts[i] < ts[i+1])

        result.append(self.propConstraints(propSet, bound))

        addTimeBound = result + partitionConsts + formula

        result = result + self.timeBoundConsts(addTimeBound, timeBound)

        return result

