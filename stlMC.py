import os, sys, io, time
import z3

from core.constraint import *
from core.stl import parseFormula
from core.z3Handler import checkSat

import core.partition as PART
import core.separation as SEP
import core.encoding as ENC


# A base class for a hybrid automaton. All models should inherit this class.
class Model:
    def __init__(self, variables, init, flow, inv, jump, prop, logic = "None"):
        self.variables = variables
        self.init = init
        self.flow = flow
        self.inv = inv
        self.jump = jump
        self.prop = prop

        self.logic = logic

        self.flowDict = self.defineFlowDict()
        self.varList = sorted(list(self.variables.keys()), key = lambda x : str(x))

    # an implementation of Algorithm 1 in the paper
    def modelCheck(self, stlFormula, bound, timeBound, iterative=True):
        (constSize, fsSize) = (0, 0)
        (stim1, etime1, stime2) = (0, 0, 0)
        isUnknown = False
        formula = parseFormula("~"+stlFormula)  # negate the formula

        for i in range(0 if iterative else bound, bound + 1):

            stime1 = time.process_time()
            # base partition
            baseP = PART.baseCase(i) 

            # partition constraint
            (partition,sepMap,partitionConsts) = PART.guessPartition(formula, baseP) 
 
            # full separation
            fs = SEP.fullSeparation(formula, sepMap)  

            # FOL translation
            baseV = ENC.baseEncoding(partition,baseP) 
            formulaConst = ENC.valuation(fs[0], fs[1], ENC.Interval(True, 0.0, True, 0.0), baseV)

            # constraints from the model
            modelConsts = self.modelConstraints(i, timeBound, partition, partitionConsts, [formulaConst])

            etime1 = time.process_time()

            # check the satisfiability
            (result, cSize) = checkSat(modelConsts + partitionConsts + [formulaConst], self.logic)

            stime2 = time.process_time()

            # calculate size
            fsSize += sum([ENC.size(f) for f in [fs[0]]+list(fs[1].values())])
            constSize += cSize

            if  result == z3.sat:
                return (False, constSize, fsSize, str(etime1-stime1), str(stime2-etime1), str(stime2-stime1))  # counterexample found
            if  result == z3.unknown:
                isUnknown = True

        return ("Unknown" if isUnknown else True, constSize, fsSize, str(etime1-stime1), str(stime2-etime1), str(stime2-stime1))


    def reach(self, bound, goal):
        consts = []
        consts.append(self.init.substitution(self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))))
        consts.append(self.flowConstraints(bound))
        consts.append(goal.substitution(self.combineDict(self.makeSubMode(bound), self.makeSubVars(bound, 't'))))
        return checkSat(consts)


    def z3TimeBoundConsts(self, consts, timeBound):
        result = []
        variables = set().union(*[c.getVars() for c in consts])
        for i in self.flow.keys():
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


    def modelConstraints(self, bound, timeBound, partition, partitionConsts, formula):
        result = []
        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, '0'))
        result.append(self.init.substitution(combine))
        result.append(self.flowConstraints(bound))

        for i in range(len(result)):
            print(result[i])

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
            result.extend(self.propConstraint(Real('time' + str(i)), i, propSet))

        result.extend(self.propConstraint(Real('time' + str(bound)), bound, propSet))
     
        addTimeBound = result + partitionConsts + formula

        result = result + self.z3TimeBoundConsts(addTimeBound, timeBound)       
 
        return result


    def combineDict(self, dict1, dict2):
        result = dict1.copy()
        for i in dict2.keys():
            result[i] = dict2[i]
        return result

    #Substitution proposition and mode variables according to bound k: {'fonepo' : fonepo_k} 
    def makeSubMode(self, k):
        op = {Type.Bool: Bool, Type.Real: Real, Type.Int: Int}
        subDict = {}
        for i in set(self.flow.keys()):
             for j in range(len(i.children)):
                 mode = i.children[j]
                 if not(isinstance(mode, Not)):
                     if (mode.getType() in op.keys()) and (not(str(mode.id) in subDict.keys())):
                         subDict[str(mode.id)] = op[mode.getType()](str(mode.id) + '_' + str(k))
        for i in self.prop.keys():
            subDict[str(i.id)] = op[i.getType()](str(i.id) + '_' + str(k))
        return subDict

    #Substituion varialbes according to bound k, sOe: var_k_0 or var_k_t
    def makeSubVars(self, k, sOe):
        op = {Type.Bool: Bool, Type.Real: Real, Type.Int: Int}
        subDict = {}
        for i in range(len(self.varList)):
            subDict[str(self.varList[i].id)] = op[self.varList[i].getType()](str(self.varList[i].id) + '_' + str(k) + '_' + sOe)
        return subDict


    def defineFlowDict(self):
        flowDict = []
        for i in set(self.flow.keys()):
            key = str(i.children).replace(",","").replace(" ","").replace("(","").replace(")","")
            flowDict.append((self.flow[i], key))
        return flowDict


    def flowDictionary(self, value):
        for i in range(len(self.flowDict)):
            if str(self.flowDict[i][0]) == str(value):
                return self.flowDict[i][0]
        return -1
        

    def flowConstraints(self, bound):
        combineJump = []
        flowConsts = []
        for k in range(bound):
            time = Real('time' + str(k))
            combineSub = self.combineDict(self.makeSubMode(k), self.makeSubVars(k, 't'))
            nextSub = self.combineDict(self.makeSubMode(k+1), self.makeSubVars(k+1, '0'))
            const = [And(i.substitution(combineSub), self.jump[i].substitution(combineSub)) for i in self.jump.keys()]
            result = [i.nextSub(nextSub) for i in const]
            combineJump.append(Or(*result))
            flowConsts.append(Or(*([And(i.substitution(self.makeSubMode(k)), Integral(self.makeSubVars(k, 't'), self.makeSubVars(k, '0'), time, str(i.children).replace(",","").replace(" ","").replace("(","").replace(")",""), self.flowDictionary(self.flow[i])), Forall(self.flowDictionary(self.flow[i]), time, self.inv[i], self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))) for i in self.flow.keys()])))

        k = bound
        time = Real('time' + str(bound))

#        flowConsts.append(Or(*([And(i.substitution(self.makeSubMode(k)), Solution(self.makeSubVars(k, 't'), self.makeSubVars(k, '0'), str(i.children).replace(",","").replace(" ","").replace("(","").replace(")",""), self.flowDictionary(self.flow[i])), Forall(self.flowDictionary(self.flow[i]), time, self.inv[i], self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))) for i in self.flow.keys()])))

        flowConsts.append(Or(*([And(i.substitution(self.makeSubMode(k)), Integral(self.makeSubVars(k, 't'), self.makeSubVars(k, '0'), time, str(i.children).replace(",","").replace(" ","").replace("(","").replace(")",""), self.flowDictionary(self.flow[i])), Forall(self.flowDictionary(self.flow[i]), time, self.inv[i], self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))) for i in self.flow.keys()])))

        return And(And(*combineJump), And(*flowConsts))

    
    def propConstraint(self, time, k, propSet):
        const = []
        for i in self.prop.keys():
            if str(i) in propSet:
                for j in self.flow.keys():
                    const.append(Implies(And(i, j).substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[j]), time, self.prop[i], self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))))
                    const.append(Implies(And(Not(i), j).substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[j]), time, Not(self.prop[i]), self.makeSubVars(k, '0'), self.makeSubVars(k, 't'), self.makeSubMode(k))))
        return const
  


