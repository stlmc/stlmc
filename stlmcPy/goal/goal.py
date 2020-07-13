import stlmcPy.core.partition as PART
import stlmcPy.core.separation as SEP
from stlmcPy.constraints.node import *
from stlmcPy.constraints.operations import get_expression
from stlmcPy.core.formula import Formula, NotFormula
import stlmcPy.core.encoding as ENC
import abc

from stlmcPy.core.node import *


class Goal:
    @abc.abstractmethod
    def make_consts(self, bound, time_bound, delta):
        pass


class StlGoal(Goal):
    # get core.formula. of some type...
    def __init__(self, formula: Formula):
        self.formula = formula
        self.modeVar = None
        self.contVar = None
        self.varVal = None
        self.modeModule = None
        self.init = None
        self.prop = None
        self.subvars = None

    def get_formula(self):
        return self.formula

    def prepare(self, modeVar, contVar, varVal, modeModule, init, prop):
        self.modeVar = modeVar
        self.contVar = contVar
        self.varVal = varVal
        self.modeModule = modeModule
        self.init = init
        self.prop = prop  # list type
        self.subvars = self.makeVariablesDict()

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

    def combineDict(self, dict1, dict2):
        result = dict1.copy()
        for i in dict2.keys():
            result[i] = dict2[i]
        return result

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

    def propForall(self, curMode, propID, exp, bound, curFlow, delta):

        combine = self.combineDict(self.makeSubMode(bound), self.makeSubProps(bound))
        combine.update(self.varVal)

        curFlowExp = get_expression(curFlow, self.subvars)
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

        return And(initPointCond,
                   Forall(curMode, propID, exp, combine, self.makeSubVars(bound, '0'), self.makeSubVars(bound, 't'),
                          subContVar, delta))

    def makePropDict(self):
        result = dict()
        for i in range(len(self.prop)):
            result[self.prop[i].getId()] = get_expression(self.prop[i], self.subvars)
        return result

    def propConstraints(self, propSet, bound, delta):
        result = list()
        for k in range(bound + 1):
            const = list()
            combine = self.combineDict(self.makeSubMode(k), self.makeSubProps(k))
            combine.update(self.varVal)
            for i in self.makePropDict().keys():
                if str(i) in propSet:
                    for m in range(len(self.modeModule)):
                        curMode = get_expression(self.modeModule[m].getMode(), self.subvars)
                        curFlow = self.modeModule[m].getFlow()
                        # const.append(self.propForall(curMode.substitution(combine), i.substitution(combine), self.makePropDict()[i], k, curFlow))
                        const.append(Implies(And(i, curMode).substitution(combine),
                                             self.propForall(curMode.substitution(combine), i.substitution(combine),
                                                             self.makePropDict()[i], k, curFlow, delta)))
                        # const.append(self.propForall(curMode.substitution(combine), Not(i).substitution(combine), Not(self.makePropDict()[i]).reduce(), k, curFlow))
                        const.append(Implies(And(Not(i), curMode).substitution(combine),
                                             self.propForall(curMode.substitution(combine),
                                                             Not(i).substitution(combine),
                                                             Not(self.makePropDict()[i]).reduce(), k, curFlow,
                                                             delta)))

            result.append(And(*const))
        return And(*result)

    def timeBoundConsts(self, consts, timeBound):
        result = []
        variables = set().union(*[c.getVars() for c in consts])
        curMode = list()
        for i in range(len(self.modeModule)):
            curMode.append(get_expression(self.modeModule[i].getMode(), self.subvars))
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

    def make_partition_consts(self, bound):
        i = bound
        negFormula = NotFormula(self.formula)
        baseP = PART.baseCase(i)

        # generate (subformula, time index) map
        (partition, sepMap) = PART.guessPartition(negFormula, baseP)

        # full separation
        fs = SEP.fullSeparation(negFormula, sepMap)

        originalFS = dict()
        for (m, n) in fs[1].keys():
            originalFS[m] = fs[1][(m, n)]

            # FOL translation
        baseV = ENC.baseEncoding(partition, baseP)
        (formulaConst, subFormulaMap) = ENC.valuation(fs[0], originalFS, ENC.Interval(True, 0.0, True, 0.0), baseV)

        # partition constraints
        return PART.genPartition(baseP, fs[1], subFormulaMap)

    def make_consts(self, bound, time_bound, delta):

        baseP = PART.baseCase(bound)
        negFormula = NotFormula(self.formula)

        (partition, sepMap) = PART.guessPartition(negFormula, baseP)
        fs = SEP.fullSeparation(negFormula, sepMap)

        originalFS = dict()
        for (m, n) in fs[1].keys():
            originalFS[m] = fs[1][(m, n)]

            # FOL translation
        baseV = ENC.baseEncoding(partition, baseP)
        (formulaConst, subFormulaMap) = ENC.valuation(fs[0], originalFS, ENC.Interval(True, 0.0, True, 0.0), baseV)

        # partition constraints
        partitionConsts = PART.genPartition(baseP, fs[1], subFormulaMap)


        stlConsts = list()
        timeConsts = list()
        ts = [Real("tau_%s" % i) for i in range(0, bound + 2)]

        timeConsts.append(ts[0] >= RealVal(0))
        timeConsts.append(Real('time0') == ts[0])

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
            timeConsts.append(Real('time' + str(i + 1)) == (ts[i + 1] - ts[i]))
            timeConsts.append(ts[i] <= ts[i + 1])

        stlConsts.append(self.propConstraints(propSet, bound, delta))

        partitionConsts = self.make_partition_consts(bound)
        addTimeBound = stlConsts + partitionConsts + [formulaConst]

        timeConsts.extend(self.timeBoundConsts(addTimeBound, time_bound))

        return stlConsts, timeConsts, partitionConsts, formulaConst, sum([ENC.size(f) for f in [fs[0]] + list(fs[1].values())])


class ReachGoal(Goal):
    # get core.formula. of some type...
    def __init__(self, formula: Formula):
        self.formula = formula

    def make_consts(self, bound, time_bound, delta):
        return self.formula
