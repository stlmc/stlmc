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
    def __init__(self):
        pass
    
    @property
    def stackID(self):
        return self._stackID

    # give file name and it will generate stackID
    # this must be invoke after data method called
    @stackID.setter
    def stackID(self, stackID):
        self._stackID = stackID + "_" + self.stl + "_" + str(self.bound)
        print("ID")
        print(self._stackID)

    @property
    def data(self):
        return self._data

    @data.setter
    def data(self, data):
        self._data = data
        (model, modeVar, contVar, subvars, props, bound, mode_module, strStlFormula) = self._data
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

    # return list of time points
    def getNumpyTimeValues(self):
        result = list()
        if self.model is not None:
            for i in range(self.bound + 1):
                declares = self.model.decls()
                for k in declares:
                    if "time" + str(i) == k.name():
                        result.append(float(self.model[k].as_decimal(6).replace("?", "")))

        t = []
        sum = 0.0
        for t_el in range(len(result) + 1):
            if t_el == len(result):
                sum_pre = sum
            else:
                sum_pre = sum
                sum += result[t_el]
            if t_el == 0:
                t.append(np.linspace(0, sum))
                print("0 ~ " + str(sum))
            else:
                print(str(sum_pre) + " ~ " + str(sum))
                t.append(np.linspace(sum_pre, sum))
        return t


    # TODO : change function name to getModeIdList
    def getModelIdList(self):
        result = []
        if self.model is not None:
            for i in range(self.bound+2):
                declares = self.model.decls()
                for k in declares:
                    if ("currentMode_" + str(i)) == k.name():
                        result.append(int(str(self.model[k])))
        #self.getSol(result)
     
        return result


    def getSolEqInitialValue(self):
        c_val = self.getContValues()
        initial_val = dict()
        for i in c_val.keys():
            subResult = []
            for j in range(self.bound + 2):
                subResult.append(c_val[i][j][0])
            initial_val[i] = subResult
        return initial_val


    def getSol(self):
        c_val = self.getContValues()
        ode_l = self.getModelIdList()
        initial_val = dict()
        for i in c_val.keys():
            subResult = []
            for j in range(self.bound+2):
                subResult.append(c_val[i][j][0])
            initial_val[i] = subResult
        print(initial_val)
        solutionBound = dict()

        #return string type {'continous id' : [sol_1, sol_2,sol_3,..,sol_bound], ...}
        '''
        for i in c_val.keys():
            solutionList = list()
            for j in range(len(ode_l)):
                modexps = self.mode_module[ode_l[j]].getFlow().exp()
                for k in range(len(modexps)):
                    if modexps[k].getVarId() == i:
                        subResult = modexps[k].getSolStr()
                        for l in initial_val.keys():
                            if l in subResult:
                                subResult = subResult.replace(l, str(initial_val[l][j]))
                        solutionList.append(subResult)
                        break
            solutionBound[i] = solutionList
        '''
        for i in c_val.keys():
            solutionList = list()
            for j in range(len(ode_l)):
                modexps = self.mode_module[ode_l[j]].getFlow().exp()
                for k in range(len(modexps)):
                    if modexps[k].getVarId() == i:
                        subResult = modexps[k]
                        solutionList.append(subResult)
                        break
            solutionBound[i] = solutionList
        print("After replacement")
        print(solutionBound)
        # solutionBound : Dict of variables and value of SolEq type object list
        # "x1": [sol_eq1, sol_eq2, ...]
        return solutionBound




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
       return idPropExp, result



    # inner function of sol equation
    # generate list that correspond to indexed interval
    def _calcSolEq(self, timeValues, model_id, index):
        # TODO : Add new functions
        sol_init_list = self.getSolEqInitialValue()
        sol_l = self.getSol()
        interval_dict = dict()

        # k is variable name of dic
        # { 'x1' : [ x1 = ..., x1 = .... , ... ] , 'x2' : ... }
        for k in sol_l:
            tmp_res = []
            self.mode_module[model_id].getFlow().var_dict[k] = sol_init_list[k][index]
            # test_res2 = []
            newT = timeValues[index].tolist()
            for i in range(len(newT)):
                self.mode_module[model_id].getFlow().time_dict["time"] = newT[i]
                tmp = list()
                tmp.append(newT[i])
                tmp += self.mode_module[model_id].getFlow().exp2exp()
                tmp_res.append(tmp)
            interval_dict[k] = tmp_res

        return interval_dict

    # buggy
    def _calcDiffEq(self, timeValues, index, var_list):
        z = []
        t = timeValues
        c_val = self.getContValues()
        for var in range(len(var_list)):
            i_val = []
            print(str(var))
            for key in var_list[var]:
                i_val.append(c_val[key][var][0])
                self.mode_module[index].getFlow().var_dict[key] = c_val[key][var][0]
            z.append(odeint(lambda z, t: self.mode_module[index].getFlow().exp2exp(), i_val, t[var]))
        return z

    def calcEq(self, timeValues):


        # get total model id
        model_id = self.getModelIdList()
        sol_l = self.getSol()
        var_list = self.intervalsVariables()

        # Get unique solEq model id list
        solEq_dict = []
        diffEq_dict = []
        for i,id in enumerate(model_id):
            if self.mode_module[id].getFlow().type == "sol":
                # check if it is in the list
                tmp = dict()
                tmp["interval"] = i
                tmp["model_id"] = id
                solEq_dict.append(tmp)

            elif self.mode_module[id].getFlow().type == "diff":
                tmp = dict()
                tmp["interval"] = i
                tmp["model_id"] = id
                diffEq_dict.append(tmp)

        res = []
        # calculation start

        #for i in model_id:
        #    if i in solEq_id:
        #        res.append(self._calcSolEq(timeValues, i))
        #    elif i in diffEq_id:
        #        res.append(self._calcDiffEq(timeValues, i, var_list))

        print("??????????????????")

        for elem in solEq_dict:
            elem["data"] = self._calcSolEq(timeValues, elem["model_id"], elem["interval"])


        for i in range(len(model_id)):
            for elem in solEq_dict:
                if elem["interval"] == i:
                    res.append(elem["data"])
            for elem in diffEq_dict:
                if elem["interval"] == i:
                    res.append(elem["data"])

        return res

    # get intervals variable list
    def intervalsVariables(self):
        model_id = self.getModelIdList()
        var_list = []
        for i in range(len(model_id)):
            var_list_tmp = []
            modexps = self.mode_module[model_id[i]].getFlow().exp()
            for j in modexps:
                var_list_tmp.append(j.var2str())
            var_list.append(var_list_tmp)
        return var_list



    def visualize(self):
        try:
            #var_list = self.getVarsId()
            print("visualize start")
            tsp = self.getTauValues()

            print("this is tau")
            print(tsp)

            '''
                if solution equation exists: 
                checking it via sol_l's length,
                first, it is parsing sol_l by key and value. (for k in sol_l line)
                second, k is variable name of dic and { 'x1' : [ x1 = ..., x1 = .... , ... ] , 'x2' : ... }
            '''

            t = self.getNumpyTimeValues()

            print("this is list")
            print(len(self.mode_module))
            outer2 = dict()
            outer2['data'] = self.calcEq(t)#outer
            print("checkpoint222")

            outer2['proplist'], outer2['prop'] = self.getProposition()
            import json
            f = open(("../visualize/src/DataDir/"+self._stackID+".json"), "w")
            json.dump(outer2, f)
            f.close()

        except Exception as ex:
            print('Nothing to draw!', str(ex))
            
