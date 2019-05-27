import z3
from core.node import *
from core.z3Handler import checkSat
import numpy as np
from scipy.integrate import odeint
import matplotlib.pyplot as plt

class Api:
    def __init__(self, model, modeVar, contVar, ODE, props, bound, flowdecl):
        self.model = model
        self.modeVar = modeVar
        self.contVar = contVar
        self.ODE = ODE
        self.props = props
        self.bound = bound
        self.flowdecl = flowdecl

    # return continuous variables id
    def getVarsId(self):
        result = []
        for i in range(len(self.contVar)):
            result.append(str(self.contVar[i].id))
        
        return result

    # return mode variables id
    def getModesId(self):
        result = []
        for i in range(len(self.modeVar)):
            result.append(str(self.modeVar[i].id))
        return result 


    # return (initial, final) pairs for each continuous variable until k bound
    def getContValues(self):
        result = {}
        if self.model is not None:
            for i in range(len(self.contVar)):
                subResult = []
                op = {'bool' : z3.Bool, 'int' : z3.Int, 'real' : z3.Real}
                for j in range(self.bound+1):
                    initial_var = op[self.contVar[i].type](str(self.contVar[i].id) + "_" + str(j) + "_0")
                    final_var = op[self.contVar[i].type](str(self.contVar[i].id) + "_" + str(j) + "_t")
                    initial_value = float(self.model[initial_var].as_decimal(6).replace("?", ""))
                    final_value = float(self.model[final_var].as_decimal(6).replace("?", ""))
                    subResult.append((initial_value, final_value))

                final_var = op[self.contVar[i].type](str(self.contVar[i].id) + "_" + str(self.bound+1) + "_0")
                final_value = float(self.model[final_var].as_decimal(6).replace("?", ""))
                subResult.append((final_value, final_value))
                 
                result[str(self.contVar[i].id)] = subResult
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
    
    def visualize(self):
        try:
            var_list = self.getVarsId()
            tsp = self.getTauValues()
            c_val = self.getContValues()
            t = np.linspace(tsp[0], tsp[1])
            print(len(tsp))
            #t = np.linspace(0, 33.3333)
#            i_val = [ 21.0 for i in range(len(var_list))]
        
            fig = plt.figure()
            s_val = c_val[var_list[0]]
            z = []
            for ikk in range(len(s_val)):
                i_val = []
                for key in c_val:
                    print(str(c_val[key][ikk][0]))
                    print(key)
                    i_val.append(c_val[key][ikk][0])
                    self.flowdecl.var_dict[key] = c_val[key][ikk][0]
                    #rrr = self.flowdecl.exp2exp()
                z.append(odeint(lambda z,t: self.flowdecl.exp2exp(), i_val, t))
                #c = ['b', 'r', 'c', 'm']
                #for i in range(len(var_list)):
            ###????????????????????????
            p = []
            for i in range(len(z)):   
                print(z[i])
                p = plt.plot(t, z[i])
                plt.axvline(x=0.5, color='r', linestyle='--', linewidth=3)
                plt.ylabel('variables')
                plt.xlabel('time')
                plt.legend(p, var_list, loc='best')
            plt.show()
    
    #        self.flowdecl.var_dict['constx1'] = 21.0
    #        self.flowdecl.var_dict['constx2'] = 21.0
    #        self.flowdecl.var_dict['x1']=0.0
    #        self.flowdecl.var_dict['x2']=0.0
    #        rrr = self.flowdecl.exp2exp()
            #print(rrr)
    #        z = odeint(lambda z,t: rrr, i_val, t)
            print("ode z : " + str(len(z)))
            # plot results
    #        c = ['b', 'r', 'c', 'm']
    #        for i in range(len(var_list)):
    #            plt.plot(t,z[:,i], c=c[i], label=var_list[i])
    #        plt.ylabel('variables')
    #        plt.xlabel('time')
    #        plt.legend(loc='best')
    #        plt.show()
        except Exception as ex:
            print('Nothing to draw!', ex)
            
