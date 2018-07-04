from core.interface import *
import os, sys, io

#from core.stl import *
#from core.partition import *
#from core.separation import *
#from core.encoding import *


class Model:
    def __init__(self, mode, variables, init, flow, inv, jump, prop):
        self.mode = mode
        self.variables = variables
        self.init = init
        self.flow = flow
        self.inv = inv
        self.jump = jump
        self.prop = prop

        self.flowDict = self.defineFlowDict()
        self.varList = list(self.variables.keys())


    def modelCheck(self, formula, bound):
        baseP = baseCase(bound)
        (partition,sepMap,partitionConsts) = guessPartition(formula, baseP)

        fs = fullSeparation(formula, sepMap)
        baseV = baseEncoding(partition,baseP)

        formulaConst = valuation(fs[0], fs[1], Interval(True, 0.0, True, 0.0), baseV)
        modelConsts = self.reach(bound)

        return partitionConsts + modelConsts + [formulaConst] 


    def reach(self, bound):
        const = []

        combine = self.combineDict(self.makeSubMode(0), self.makeSubVars(0, 0))
        const.append(self.init.substitution(combine))

        ts = [Real("tau_%s"%i) for i in range(bound)]
        const.append(ts[0] >= RealVal(0))

        for i in range(bound - 1):
            const.append(Real('time' + str(i)) == (ts[i+1] - ts[i]))
            const.extend(self.flowHandler(Real('time' + str(i)), i))
            const.extend(self.invHandler(Real('time' + str(i)), i))
            const.extend(self.jumpHandler(i))
            const.append(ts[i] < ts[i+1])
            const.extend(self.propHandler(Real('time' + str(i)), i))

        return const


    def combineDict(self, dict1, dict2):
        result = dict1.copy()
        for i in dict2.keys():
            result[i] = dict2[i]
        return result

    def makeSubMode(self, k):
        op = {Type.Bool: Bool, Type.Real: Real, Type.Int: Int}
        subDict = {}
        for i in range(len(self.mode)):
            subDict[str(self.mode[i].id)] = op[self.mode[i].getType()](str(self.mode[i].id) + '_' + str(k))
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
        count = 1
        flowDict = []
        for i in set(self.flow.keys()):
            flowDict.append((self.flow[i], count))
            count += 1
        return flowDict

    def flowDictionary(self, value):
        for i in range(len(self.flowDict)):
            if str(self.flowDict[i][0]) == str(value):
                return self.flowDict[i][1]
        return -1
        
    

    def flowHandler(self, time, k):
        const = [Implies(i.substitution(self.makeSubMode(k)), Integral(self.makeSubVars(k, 1), self.makeSubVars(k,0), time, self.flowDictionary(self.flow[i]), self.flow[i])) for i in self.flow.keys()]
        return const
         
    def invHandler(self, time, k):
        const = [Implies(i.substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[i]), time, self.inv[i], self.makeSubVars(k, 0), self.makeSubVars(k, 1), self.makeSubMode(k))) for i in self.inv.keys()]
        return const

    def propHandler(self, time, k):
        const = []
        for i in self.prop.keys():
            proconst = []
            notproconst = []
            for j in self.flow.keys():
                proconst.append(And(And(i, j).substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[j]), time, self.prop[i], self.makeSubVars(k, 0), self.makeSubVars(k, 1), self.makeSubMode(k))))
                notproconst.append(And(And(Not(i), j).substitution(self.makeSubMode(k)), Forall(self.flowDictionary(self.flow[j]), time, Not(self.prop[i]), self.makeSubVars(k, 0), self.makeSubVars(k, 1), self.makeSubMode(k))))
            const.append(Or(proconst))
            const.append(Or(notproconst))

        return const
  

    def jumpHandler(self, k):
        combineSub = self.combineDict(self.makeSubMode(k), self.makeSubVars(k, 1))
        nextSub = self.combineDict(self.makeSubMode(k+1), self.makeSubVars(k+1, 0))
        const = [Implies(i.substitution(combineSub), self.jump[i].substitution(combineSub)) for i in self.jump.keys()]
        result = [i.nextSub(nextSub) for i in const]
        return result

