from .error import *
from .TYPE import *

class dRealHandler:
    def __init__(self, const, output, varRange, defineODE):
        self.const = const
        self.defineODE = defineODE
        self.output = output
        self.varRange = varRange

    def addConst(self, constList):
        self.const += constList

    def ODEDeclareHandler(self):
        self.output.write("(set-logic QF_NRA_ODE)\n")
        for i in self.varRange.keys():
            self.output.write("(declare-fun ")
            self.output.write(str(i.id))
            self.output.write(" () Real [" + str(self.varRange[i][0]) + ", " + str(self.varRange[i][1]) + "])\n")
        for i in range(len(self.defineODE)):
            self.output.write("(define-ode flow_" + str(self.defineODE[i][1]) + " (")
            for j in self.defineODE[i][0].keys():
                self.output.write("(= d/dt[" + str(j) + "] " + str(self.defineODE[i][0][j]) + ")\n                 ")
            self.output.write("))\n")

    def varsDeclareHandler(self):

        variables = set().union(*[c.getVars() for c in self.const])
        for i in self.varRange.keys():
            if i in variables:
                variables.remove(i)
        variables = list(variables)

        for i in range(len(variables)):
            self.output.write("(declare-fun ")
            self.output.write(str(variables[i]))
            self.output.write(" () ")
            typeName = str(variables[i].getType().name)
            keyIndex = str(variables[i]).find('_')
            self.output.write(typeName)
            key = str(variables[i])[:keyIndex]
            strRange = {}
            for i in self.varRange.keys():
                strRange[str(i.id)] = self.varRange[i]
            if key in strRange.keys():
                self.output.write(" [" + str(strRange[key][0]) + ", " + str(strRange[key][1]) + "]")
            elif typeName == 'Real':
                self.output.write(" [0.0000, 1000.0000]")
            self.output.write(")\n")

    def assertDeclareHandler(self):
        for i in range(len(self.const)):
            self.output.write("(assert " + repr(self.const[i]) + ")\n")

    def satHandler(self):
        self.output.write("(check-sat)\n")

    
    def exitHandler(self):
        self.output.write("(exit)\n")

    def callAll(self):
        self.ODEDeclareHandler()
        self.varsDeclareHandler()
        self.assertDeclareHandler()
        self.satHandler()
        self.exitHandler()

