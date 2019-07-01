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
    def __init__(self, model, modeVar, contVar, subvars, props, bound, mode_module):
        self.model = model
        self.modeVar = modeVar
        self.contVar = contVar
        self.subvars = subvars
        self.props = props
        self.bound = bound
        self.mode_module = mode_module
        self.IDmodeModule = {}
        for k in range(len(self.mode_module)):
            self.IDmodeModule[k] = self.mode_module[k]

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

       if self.model is not None:
           for i in range(self.bound+2):
               getModeConsts = []
               for j in self.getModesId():
                   declares = self.model.decls()
                   for k in declares:
                       if (j + "_" + str(i)) == k.name():
                           if isinstance(self.model[k], z3.z3.BoolRef):
                               getModeConsts.append(Bool(k.name()[:-2]) == BoolVal(True if str(self.model[k]) == "True" else False))
                           else:
                               getModeConsts.append(Real(k.name()[:-2]) == RealVal(self.model[k]))
                           declares.remove(k)

               for k in range(len(self.mode_module)):
                   mode = self.IDmodeModule[k].getMode().getExpression(self.subvars)
                   getModeConsts.append(mode)
                   coincide = checkSat(getModeConsts)[0]
                   if coincide == z3.sat:
                       result.append(k)
                       break
                   getModeConsts.pop()


           #check matched modeModule’s mode
           #for i in range(len(result)):
           #    print(self.IDmodeModule[result[i]])

       return result


    def getProposition(self):
       result = {}
       idPropExp = {}
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
               if idCheck and (len(subResult) > 0):
                   result[str(self.props[i].getId())] = subResult
                   idPropExp[str(self.props[i].getId())] = str(self.props[i].getExpStr())
       print(idPropExp)
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
                modexps = self.mode_module[ode_l[i]].getFlow().exp()
                for j in modexps:
                    var_list_tmp.append(j.var2str())
                var_list.append(var_list_tmp)

            #print(var_list)

            #ode_effective = self.ODE()
            '''
            for i in range(len(ode_l)):
                var_list_tmp = []
                for j in ode_l[i]:
                    x = j.split("=")
                    var_list_tmp.append(x[0].replace(" ", ""))
                var_list.append(var_list_tmp)
            '''
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
                    print("0 ~ "+str(sum))
                else:
                    print(str(sum_pre) + " ~ " + str(sum))
                    t.append(np.linspace(sum_pre, sum))
            fig = plt.figure()
            z = []
            print("start")
            print(c_val)
            print(str(len(self.mode_module)))
            for var in range(len(var_list)):
                i_val = []
                print(str(var))
                for key in var_list[var]:
                    print("meme => "+str(var)+"===>"+str(c_val[key][var][0]))
                    i_val.append(c_val[key][var][0])
                    self.mode_module[ode_l[var]].getFlow().var_dict[key] = c_val[key][var][0]
                    print("meme end =>"+str(var))
                    #print("Time iter: "+str(var)+" and var iter: "+str(c_val[key][var][0])+" ival:"+str(i_val)+" time t list:"+str(t[var]))
                z.append(odeint(lambda z,t: self.mode_module[ode_l[var]].getFlow().exp2exp(), i_val, t[var]))
            p = []
            vv = []
            d_ttt = dict()
            d_ttt['var'] = var_list
            # time space array and data array size must be same!
            # len(t) === len(z)
            outer=[]
            for i in range(len(var_list)):
                d_ttt2=dict()
                for k in range(len(var_list[i])):
                    inner=[]
                    for j in range(len(z[i])):
                        pair = []
                        pair.append(t[i][j])
                        pair.append(z[i][j][k])
                        inner.append(pair)
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
            f.close()
            plt.show()
    
            print("ode z : " + str(len(z)))
        except Exception as ex:
            print('Nothing to draw!', str(ex))
            
