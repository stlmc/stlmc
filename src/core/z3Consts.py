import z3
import core.encoding as ENC
from .node import *
from .z3Handler import *

class z3Consts:
    def __init__(self, modeVar, contVar, modeModule, init, propositions, substitutionVars):
        self.modeVar = modeVar
        self.contVar = contVar
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
            combine = self.combineDict(self.makeSubVars(k, '0'), self.makeSubVars(k, 't'))
            for i in range(len(self.contVar)):
                result.append(self.contVar[i].getConstraint().substitution(combine))
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
            '''
            steadyStateConsts = list()
            op = {'bool' : Bool, 'int' : Int, 'real' : Real}
            for k in range(len(self.modeVar)):
                mode = op[self.modeVar[k].getType()](self.modeVar[k].getId())
                steadyStateConsts.append(NextVar(mode) == mode)
            for k in range(len(self.contVar)):
                var = op[self.contVar[k].getType()](self.contVar[k].getId())
                steadyStateConsts.append(NextVar(var) == var)
            subresult.append(And(*steadyStateConsts))
            '''
            if (len(subresult) > 0):
                jumpConsts.append(And(self.modeModule[i].getMode().getExpression(self.subvars), Or(*subresult)))

        result = []
        for k in range(bound+1):
            time = Real('time' + str(k))

            combineSub = self.combineDict(self.makeSubMode(k), self.makeSubVars(k, 't'))
            nextSub = self.combineDict(self.makeSubMode(k+1), self.makeSubVars(k+1, '0'))

            const = [i.substitution(combineSub) for i in jumpConsts]
            combineJump = [i.nextSub(nextSub) for i in const]
            if len(combineJump) > 0 :
                result.append(Or(*combineJump))

        if len(result) > 0:
            return And(*result)
        return BoolVal(True)

    def flowConstraints(self, bound):
        result= list()
        for k in range(bound+1):
            time = Real('time' + str(k))
            flowConsts = list()
            for i in range(len(self.modeModule)):
                flowModule = dict()
                curMode = self.modeModule[i].getMode().getExpression(self.subvars)
                curFlow = self.modeModule[i].getFlow().getExpression(self.subvars)
                for j in range(len(curFlow)):
                    if curFlow[j].getVarId() in self.subvars.keys():
                        flowModule[self.subvars[curFlow[j].getVarId()]] = curFlow[j].getFlow(self.subvars)
                    else:
                        raise ("Flow id is not declared")
                modeConsts = list()
                for otherModeID in range(0, i):
                    modeConsts.append(Not(Int('currentMode_'+str(k)) == IntVal(otherModeID)))
                for otherModeID in range(i+1, len(self.modeModule)):
                    modeConsts.append(Not(Int('currentMode_'+str(k)) == IntVal(otherModeID)))

#                modeConsts.append(And(Real('currentMode_'+str(k)) >= RealVal(i), Real('currentMode_'+str(k)) <= RealVal(i)))

                modeConsts.append(Int('currentMode_'+str(k)) == IntVal(i))
                modeConsts.append(Int('currentMode_'+str(k)) < IntVal(len(self.modeModule)))
                modeConsts.append(Int('currentMode_'+str(k)) >= IntVal(0))
                modeConsts.append(curMode.substitution(self.makeSubMode(k)))

                modeConsts.append(And(curMode.substitution(self.makeSubMode(k)), Integral(self.makeSubVars(k, 't'), self.makeSubVars(k, '0'), time, flowModule, self.modeModule[i].getFlow().getFlowType())))

                flowConsts.append(And(*modeConsts))
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

    def goalConstraints(self, bound, goal):
        combine = self.combineDict(self.makeSubMode(bound), self.makeSubVars(bound, 't'))
        return goal.substitution(combine)

    def propConstraints(self, propSet, bound):
        result = list()
        for k in range(bound+1):
            time = Real('time' + str(k))
            const = list()
            combine = self.combineDict(self.makeSubMode(k), self.makeSubProps(k))
            for i in self.makePropDict().keys():
                if str(i) in propSet:
                    for m in range(len(self.modeModule)):
                        flowModule = dict()
                        curMode = self.modeModule[m].getMode().getExpression(self.subvars)
                        const.append(Implies(And(i, curMode).substitution(combine), Forall(time, self.makePropDict()[i], self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))))
                        const.append(Implies(And(Not(i), curMode).substitution(combine), Forall(time, Not(self.makePropDict()[i]), self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))))
            result.append(And(*const))
        return And(*result)

    def z3TimeBoundConsts(self, consts, timeBound):
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
            if (key.find('time') != -1): 
                result.append(variables[i] > RealVal(0))
                result.append(variables[i] <= RealVal(timeBound))
            if (key.find('tau') != -1 or key.find('TauIndex') != -1):
                result.append(variables[i] >= RealVal(0))
                result.append(variables[i] <= RealVal(timeBound))
        return result

    # Make constraints of the model
    def modelConstraints(self, bound, timeBound, partition, partitionConsts, formula):
        result = list()
        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))
        result.append(self.makeVarRangeConsts(bound)) # make range constraint
        result.append(self.init.getExpression(self.subvars).substitution(combine)) # make initial constraint
        result.append(self.flowConstraints(bound))
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

        result = result + self.z3TimeBoundConsts(addTimeBound, timeBound)

        return result
