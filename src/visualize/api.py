import z3
from core.node import *
from core.z3Handler import checkSat
import numpy as np
from scipy.integrate import odeint
# add mac dependency
# that use TkAgg
import matplotlib
matplotlib.use('TkAgg')
import matplotlib.pyplot as plt


class Api:
    def __init__(self, model, modeVar, contVar, ODE, props, bound, mode_module):
        self.model = model
        self.modeVar = modeVar
        self.contVar = contVar
        self.ODE = ODE
        self.props = props
        self.bound = bound
        self.mode_module = mode_module

    def setStrStlFormula(self, strStlFormula):
        self.stl = strStlFormula

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
                    if "time" + str(i) == k.name():
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
                propID = str(self.props[i].getId())
                idCheck = (propID in self.stl) or ("newPropDecl_" in propID)
                for j in range(self.bound+2):
                    declares = self.model.decls()
                    for k in declares:
                        if idCheck and (propID + "_" + str(j) == k.name()):
                            subResult.append(str(self.model[k]))
                            declares.remove(k)
                if idCheck: 
                    result[str(self.props[i].getId())] = subResult
        return result 
    
    def visualize(self):
        try:
            #var_list = self.getVarsId()
            var_list = []
            tsp = self.getTauValues()
            c_val = self.getContValues()
            ode_l = self.getODE()
            for i in range(len(ode_l)):
                var_list_tmp = []
                for j in ode_l[i]:
                    x = j.split("=")
                    var_list_tmp.append(x[0].replace(" ", ""))
                var_list.append(var_list_tmp)

            t = []
            sum = 0.0
            sum_pre = 0.0
            for t_el in range(len(tsp)+1):
                if t_el == len(tsp):
                    sum_pre = sum
                else:
                    sum_pre = sum
                    sum += tsp[t_el]
                if t_el == 0:
                    t.append(np.linspace(0, sum))
                    #t_tmp = list()
                    #t_tmp.append(0)
                    #t_tmp.append(sum)
                    #print(t_tmp)
                    #t.append(t_tmp)
                    print("0 ~ "+str(sum))
                else:
                    #t_tmp = list()
                    #t_tmp.append(sum_pre)
                    #t_tmp.append(sum)
                    #print(t_tmp)
                    print(str(sum_pre) + " ~ " + str(sum))
                    t.append(np.linspace(sum_pre, sum))
            #t.append(np.linspace(sum, sum))
            fig = plt.figure()
            z = []
            for var in range(len(var_list)):
                i_val = []
                for key in var_list[var]:
                    i_val.append(c_val[key][var][0])
                    self.mode_module[var].getFlow().var_dict[key] = c_val[key][var][0]
                z.append(odeint(lambda z,t: self.mode_module[var].getFlow().exp2exp(), i_val, t[var]))
                #c = ['b', 'r', 'c', 'm']
                #for i in range(len(var_list)):
            p = []
            vv = []
            d_ttt = dict()
            d_ttt['var'] = var_list
            #d_ttt2 = dict()
            #d_ttt3 = dict()
            # time space array and data array size must be same!
            # len(t) === len(z)
            outer=[]
            for i in range(len(var_list)):
                #outer=[]
                d_ttt2=dict()
                for k in range(len(var_list[i])):
                    inner=[]
                    for j in range(len(z[i])):
                        pair = []
                        pair.append(t[i][j])
                        pair.append(z[i][j][k])
                        inner.append(pair)
                    #outer.append(inner)
                    d_ttt2[var_list[i][k]] = inner
                outer.append(d_ttt2)    
            print(outer)
            outer2 = dict()
            outer2['data'] = outer
            print(self.getProposition())
            outer2['prop'] = self.getProposition()
            
            for i in range(len(z)):   
                print(z[i])
                d_ttt[str(i)] = z[i].tolist()
                p = plt.plot(t[i], z[i])
                plt.axvline(x=0.5, color='r', linestyle='--', linewidth=3)
                plt.ylabel('variables')
                plt.xlabel('time')
                plt.legend(p, var_list, loc='best')
            import json
            f = open("../visualize/src/DataDir/test.json", "w")
            json.dump(outer2, f)
#            print(json.dump(d_ttt, f))
            f.close()
            plt.show()
    
    #        self.flowdecl.var_dict['constx1'] = 21.0
    #        self.flowdecl.var_dict['constx2'] = 21.0
    #        self.flowdecl.var_dict['x1']=21.0
    #        self.flowdecl.var_dict['x2']=21.0
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
            
