import os, sys, io
from core.constraint import *
from core.stl import *
from core.partition import *
from core.separation import *
from core.encoding import *
import z3
from core.z3Handler import *

class Model:
    def __init__(self, variables, init, flow, inv, jump, prop, time, stl, filename, goal):
        self.variables = variables
        self.init = init
        self.flow = flow
        self.inv = inv
        self.jump = jump
        self.prop = prop
        self.goal = goal
        self.time = time
        self.stl = stl
        self.filename = filename

        self.flowDict = self.defineFlowDict()
        prevarList = list(self.variables.keys())

        self.varList = sorted(prevarList, key = lambda x : str(x))

    def modelCheck(self, formula, bound):
        baseP = baseCase(bound)
        (partition,sepMap,partitionConsts) = guessPartition(formula, baseP)

        fs = fullSeparation(formula, sepMap)
        baseV = baseEncoding(partition,baseP)

        formulaConst = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseV)
        fsSize = sum([size(f) for f in [fs[0]]+list(fs[1].values())])

        modelConsts = []

        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, 0))
        modelConsts.append(self.init.substitution(combine))

        for i in range(bound):
            modelConsts.append(self.BeforeflowHandler(Real('time' + str(i)), i))

        modelConsts.append(self.AfterflowHandler(Real('time' + str(bound)), bound))

        if bound == 0:
            ts = [Real("tau_0")]
        else:
            ts = [Real("tau_%s"%i) for i in range(bound+1)]

        modelConsts.append(ts[0] >= RealVal(0))
        modelConsts.append(Real('time0') == ts[0])

        propSet = set() 
        for f in partition.keys():
            if isinstance(f, PropositionFormula):
               propSet.add(str(f))

        for i in range(bound):
            modelConsts.append(Real('time' + str(i+1)) == (ts[i+1] - ts[i]))
            modelConsts.append(ts[i] < ts[i+1])
            modelConsts.extend(self.propHandler(Real('time' + str(i)), i, propSet))

        modelConsts.extend(self.propHandler(Real('time' + str(bound)), bound, propSet))
        return (modelConsts, partitionConsts, formulaConst, fsSize) 


    def reach(self, bound):
        const = []

        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, 0))
        const.append(self.init.substitution(combine))

        for i in range(bound):
            const.append(self.BeforeflowHandler(Real('time' + str(i)), i))

        const.append(self.AfterflowHandler(Real('time' + str(bound)), bound))

        combine = self.combineDict(self.makeSubMode(bound), self.makeSubVars(bound, 1))
        const.append(self.goal.substitution(combine))
        z3model = [z3Obj(i) for i in const]
        s = z3.Solver()
        s.add(z3model)
        print("reach " + str(s.check()))
        return const


    def combineDict(self, dict1, dict2):
        result = dict1.copy()
        for i in dict2.keys():
            result[i] = dict2[i]
        return result

    def makeSubMode(self, k):
        op = {Type.Bool: Bool, Type.Real: Real, Type.Int: Int}
        subDict = {}
        for i in self.prop.keys():
            subDict[str(i.id)] = op[i.getType()](str(i.id) + '_' + str(k))
        return subDict

    def makeSubVars(self, k, sOe):
        op = {Type.Bool: Bool, Type.Real: Real, Type.Int: Int}
        subDict = {}
        for i in range(len(self.varList)):
            if sOe == 0:
                subDict[str(self.varList[i].id)] = op[self.varList[i].getType()](str(self.varList[i].id) + '_' + str(k) + '_0')
            elif sOe == 1:
                subDict[str(self.varList[i].id)] = op[self.varList[i].getType()](str(self.varList[i].id) + '_' + str(k) + '_t')
            else:
                pass
        return subDict

    def defineFlowDict(self):
        flowDict = []
        for i in set(self.flow.keys()):
            flowDict.append((self.flow[i], i.children[1]))
        return flowDict

    def flowDictionary(self, value):
        for i in range(len(self.flowDict)):
            if str(self.flowDict[i][0]) == str(value):
                return self.flowDict[i][0]
        return -1
        
    
    def BeforeflowHandler(self, time, k):
        combineSub = self.combineDict(self.makeSubMode(k), self.makeSubVars(k, 1))
        nextSub = self.combineDict(self.makeSubMode(k+1), self.makeSubVars(k+1, 0))
        const = [And(i.substitution(combineSub), self.jump[i].substitution(combineSub)) for i in self.jump.keys()]
        result = [i.nextSub(nextSub) for i in const]
        result = Or(*result)
        const = [And(i.substitution(self.makeSubMode(k)), Integral(self.makeSubVars(k, 1), self.makeSubVars(k,0), time, i.children[1], self.flowDictionary(self.flow[i])), Forall(self.flowDictionary(self.flow[i]), time, self.inv[i], self.makeSubVars(k, 0), self.makeSubVars(k, 1), self.makeSubMode(k))) for i in self.flow.keys()]
        constresult = []
        for i in const:
            constresult.append(And(i, result))
        return Or(*constresult)

    def AfterflowHandler(self, time, k):
        const = [And(i.substitution(self.makeSubMode(k)), Integral(self.makeSubVars(k, 1), self.makeSubVars(k,0), time, i.children[1], self.flowDictionary(self.flow[i])), Forall(self.flowDictionary(self.flow[i]), time, self.inv[i], self.makeSubVars(k, 0), self.makeSubVars(k, 1), self.makeSubMode(k))) for i in self.flow.keys()]
        return Or(*const)

    def propHandler(self, time, k, propSet):
        const = []
        for i in self.prop.keys():
            if str(i) in propSet:
                for j in self.flow.keys():
                    const.append(Implies(And(i, j).substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[j]), time, self.prop[i], self.makeSubVars(k, 0), self.makeSubVars(k, 1), self.makeSubMode(k))))
                    const.append(Implies(And(Not(i), j).substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[j]), time, Not(self.prop[i]), self.makeSubVars(k, 0), self.makeSubVars(k, 1), self.makeSubMode(k))))
        return const
  


