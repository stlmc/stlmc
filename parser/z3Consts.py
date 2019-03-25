import z3
import os, sys
sys.path.append(os.path.dirname(os.path.abspath(os.path.dirname(__file__))))
from core.constraint import *
import core.encoding as ENC

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
                curFlow = self.modeModule[i].getFlow().getExpression(self.subvars)
                for j in range(len(curFlow)):
                    if curFlow[j].getVarId() in self.subvars.keys():
                        flowModule[self.subvars[curFlow[j].getVarId()]] = curFlow[j].getFlow(self.subvars)
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
                    for m in range(len(self.modeModule)):
                        flowModule = dict()
                        curMode = self.modeModule[m].getMode().getExpression(self.subvars)
                        const.append(Implies(And(i, curMode).substitution(self.makeSubMode(k)), Forall(time, self.makePropDict()[i], self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))))
                        const.append(Implies(And(Not(i), curMode).substitution(self.makeSubMode(k)), Forall(time, Not(self.makePropDict()[i]), self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))))
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
            if (key.find('time') != -1 or key.find('tau') != -1 or key.find('TauIndex') != -1):
                result.append(variables[i] >= RealVal(0))
                result.append(variables[i] <= RealVal(timeBound))
        return result

    # Make constraints of the model
    def modelConstraints(self, bound, timeBound, partition, partitionConsts, formula):
        result = list()
        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))
        result.append(self.makeVarRangeConsts()) # make range constraint
        result.append(self.init.getExpression(self.subvars).substitution(combine)) # make initial constraint
        result.append(self.flowConstraints(bound))

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
