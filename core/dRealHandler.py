from .constraint import *

class dRealHandler:
    def __init__(self, const, output, varList, varRange, defineODE, modeRange, time, k):
        self.const = const
        self.defineODE = defineODE
        self.output = output
        self.varRange = varRange
        self.modeRange = modeRange
        self.varList = varList
        self.time =time
        self.k = k

    def addConst(self, constList):
        self.const += constList

    def ODEDeclareHandler(self):
        self.output.write("(set-logic QF_NRA_ODE)\n")
        for i in self.varList:
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
        preVariables = list(variables)
        variables = sorted(preVariables, key = lambda x : str(x))

        for i in range(len(variables)):
            self.output.write("(declare-fun ")
            self.output.write(str(variables[i]))
            self.output.write(" () ")
            typeName = str(variables[i].getType().name)
            keyIndex = str(variables[i]).find('_')
            self.output.write(typeName)
            key = str(variables[i])[:keyIndex]
            strRange = {}
            mstrRange = {}
            for i in self.varRange.keys():
                strRange[str(i.id)] = self.varRange[i]
            for i in self.modeRange.keys():
                mstrRange[str(i.id)] = self.modeRange[i]
            if key in strRange.keys():
                self.output.write(" [" + str(strRange[key][0]) + ", " + str(strRange[key][1]) + "]")
            elif typeName == 'Bool':
                pass
            elif key in mstrRange.keys():
                self.output.write(" [" + str(mstrRange[key][0]) + ", " + str(mstrRange[key][1]) + "]")
            elif key.find('time') != -1:
                self.output.write(" [0, " + str(self.time) + "]")
            elif key.find('tau') != -1:
                self.output.write(" [0, " + str(self.time * (self.k + 3)) + "]")
            elif key.find('TauIndex') != -1:
                self.output.write(" [0, " + str(self.time * (self.k + 3)) + "]")
            else:
                pass
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

