import dreal
from .node import *

'''
We cannot generate formula when initialized
since, it needs context before generate formula.

vars: variable list
var_condition: list of vars conditions
condition: condition..
'''
class Dreal4Forall(Node):
    def __init__(self, props, k, curFlow):
        self.props = props
        self.k = k
        self.curFlow = curFlow
        # self.vars = vars
        # self.var_condition = var_condition
        # self.condition = condition

        # newVars = list()
        # for var in vars:
        #     newVars.append(Variable(var))
        # drealVars = Variables(newVars)
        # formula = var_condition.append(forall(drealVars, condition))
        # self._formula = And(*formula)
        super().__init__(Type.Bool)

    def getVars(self):
        return set()
    # @property
    # def formula(self):
    #     return self._formula

    # # see...
    # def __repr__(self):
    #     if not self.condition.getVars():
    #         result = ""
    #     elif str(list(self.condition.getVars())[0]) in self.modeDict.keys():
    #         subCondition = self.condition.substitution(self.modeDict)
    #         result = str(subCondition)
    #     else:
    #         endCond = self.condition.substitution(self.endDict)
    #         startCond = self.condition.substitution(self.startDict)
    #         constraint = And(endCond, startCond).substitution(self.modeDict)
    #         #            result = '(and ' + str(constraint) + ' (forall_t ' + self.flowIndex + ' [0. ' + str(self.time) + '] ' + str(endCond.substitution(self.modeDict)) + '))'
    #         result = '(and ' + str(constraint) + ' (forall_t ' + ' [0. ' + str(self.time) + '] ' + str(
    #             endCond.substitution(self.modeDict)) + '))'
    #     return result