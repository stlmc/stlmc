import z3
from .node import *
from .z3Handler import checkSat

class Api:
    def __init__(self, model, modeVar, contVar, ODE, props, bound):
        self.model = model
        self.modeVar = modeVar
        self.contVar = contVar
        self.ODE = ODE
        self.props = props
        self.bound = bound

    # return continuous variables id
    def getVarsId(self):
        result = []
        for i in range(len(self.contVar)):
            result.append(str(self.contVar[i].getId()))
        
        return result

    # return mode variables id
    def getModesId(self):
        result = []
        for i in range(len(self.modeVar)):
            result.append(str(self.modeVar[i].getId()))
        return result 


    # return (initial, final) pairs for each continuous variable until k bound
    def getContValues(self):
        result = {}
        if self.model is not None:
            for i in range(len(self.contVar)):
                subResult = []
                for j in range(self.bound+2):
                    declares = self.model.decls()
                    for k in declares:
                        if str(self.contVar[i].getId()) + "_" + str(j) + "_0" == k.name():
                            initial = float(self.model[k].as_decimal(6).replace("?", ""))
                            declares.remove(k)
                        elif str(self.contVar[i].getId()) + "_" + str(j) + "_t" == k.name():
                            final = float(self.model[k].as_decimal(6).replace("?", ""))
                            declares.remove(k)
                    subResult.append((initial, final))
                result[str(self.contVar[i].getId())] = subResult
        return result

    # return list of variable point times
    def getTauValues(self):
        result = list()
        if self.model is not None:
            for i in range(self.bound+1):
                declares = self.model.decls()
                for k in declares:
                    if "tau_" + str(i) == k.name():
                        result.append(float(self.model[k].as_decimal(6).replace("?", "")))
        return result
   
    def getODE(self):
        result = []
        modeResult = []
        if self.model is not None:
            for i in range(self.bound+2):
                getModeConsts = []
                curModeValue = {}
                for j in self.getModesId():
                    declares = self.model.decls()
                    for k in declares:
                        if (j + "_" + str(i)) == k.name():
                            if isinstance(self.model[k], z3.z3.BoolRef):
                                curModeValue[k.name()] = self.model[k]
                                getModeConsts.append(Bool(k.name()[:-2]) == BoolVal(True if str(self.model[k]) == "True" else False))
                            else:
                                curModeValue[k.name()] = float(self.model[k].as_decimal(6).replace("?", ""))
                                getModeConsts.append(Real(k.name()[:-2]) == RealVal(self.model[k]))
                            declares.remove(k)

                for k in self.ODE.keys():
                    getModeConsts.append(k)
                    coincide = checkSat(getModeConsts)[0]
                    if coincide == z3.sat:
                        toString = list()
                        for m in range(len(self.ODE[k])):
                            toString.append(str(self.ODE[k][m]))
                        result.append(toString)
                        break
                    getModeConsts.pop()

                modeResult.append(curModeValue)   
        return result

    def getProposition(self):
        result = {}
        if self.model is not None:
            for i in range(len(self.props)):
                subResult = []
                for j in range(self.bound+2):
                    declares = self.model.decls()
                    for k in declares:
                        if str(self.props[i].getId()) + "_" + str(j) == k.name():
                            subResult.append(self.model[k])
                            declares.remove(k)
                result[str(self.props[i].getId())] = subResult
        return result 
     
