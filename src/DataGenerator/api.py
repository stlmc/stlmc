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
        #print("ID")
        #print(self._stackID)

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
    def getModesIdDict(self):
        result = {}
        for i in range(len(self.modeVar)):
           result[str(self.modeVar[i].id)] = (list(), str(self.modeVar[i].type))
        return result

    # return mode declaraion to string
    def getModeDeclWithModelID(self):
        idList = self.getModelIdList()
        modeIdDict = self.getModesIdDict()
        result = []
        for i in range(len(idList)):
            conditions = self.mode_module[idList[i]].getMode().props
            for j in range(len(conditions)):
                if conditions[j].left in modeIdDict.keys():
                    if modeIdDict[conditions[j].left] is None:
                        modeIdDict[conditions[j].left][0] = [str(conditions[j].right)]
                    else:
                        modeIdDict[conditions[j].left][0].extend([str(conditions[j].right)])
        result = list()
        for key in modeIdDict.keys():
            dictElement = dict()
            dictElement["name"] = key
            dictElement["type"] = modeIdDict[key][1]
            dictElement["data"] = modeIdDict[key][0]
            result.append(dictElement)
        return result, idList


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
                if self.model[final_var] is not None:
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
    def getNumpyGlobalTimeValues(self):
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
                #print("0 ~ " + str(sum))
            else:
                #print(str(sum_pre) + " ~ " + str(sum))
                t.append(np.linspace(sum_pre, sum))
        return t

    # return list of interval's time points
    def getNumpyLocalTimeValues(self):
        result = list()
        if self.model is not None:
            for i in range(self.bound + 1):
                declares = self.model.decls()
                for k in declares:
                    if "time" + str(i) == k.name():
                        result.append(float(self.model[k].as_decimal(6).replace("?", "")))

        t = []
        for t_el in range(len(result)):
            t.append(np.linspace(0, result[t_el]))
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
        #print(initial_val)
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
        #print("After replacement")
        #print(solutionBound)
        # solutionBound : Dict of variables and value of SolEq type object list
        # "x1": [sol_eq1, sol_eq2, ...]
        return solutionBound




    def getProposition(self):
       result = []
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
                   # result is for { "prop": [values...] }
                   # value is in form of { "Name": "disl10", "Actual": "x2-x1 < 10", "Data": ["True", "False"] }
                   # value
                   resultVal = dict()
                   resultVal["name"] = str(self.props[i].getId())
                   resultVal["actual"] = str(self.props[i].getExpStr())
                   resultVal["data"] = subResult
                   result.append(resultVal)
       return result



    # inner function of sol equation
    # generate list that correspond to indexed interval
    def _calcSolEq(self, global_timeValues, local_timeValues, model_id, index):
        # TODO : Add new functions
        sol_init_list = self.getSolEqInitialValue()
        sol_l = self.getSol()

        interval_list = []


        # k is variable name of dic
        # { 'x1' : [ x1 = ..., x1 = .... , ... ] , 'x2' : ... }
        for k in sol_l:
            interval_dict = dict()
            tmp_res = []
            self.mode_module[model_id].getFlow().var_dict[k] = sol_init_list[k][index]
            global_newT = global_timeValues[index].tolist()
            local_newT = local_timeValues[index].tolist()
            # modify this to use given initial value and time pairs
            for i in range(len(local_newT)):
                self.mode_module[model_id].getFlow().time_dict["time"] = local_newT[i]
                # this line makes point pair. For example, below lines will makes
                # pair { "x": 0.0, "y": 20.0 }. "global_newT[i]" is correspond to x value and
                # "self.mode_module[model_id].getFlow().exp2exp()" is correspond to y value
                # but for some reason "self.mode_module[model_id].getFlow().exp2exp()" itself
                # contains [value]. So we need to remove list before putting it inside tmp dictionary.
                # That is why we use "self.mode_module[model_id].getFlow().exp2exp()[0]" instead.
                tmp = dict()
                tmp["x"] = global_newT[i]
                tmp["y"] = self.mode_module[model_id].getFlow().exp2exp()[0]
                tmp_res.append(tmp)
            interval_dict["name"] = k
            interval_dict["intIndex"] = index
            interval_dict["points"] = tmp_res
            interval_list.append(interval_dict)

        return interval_list, global_newT

    # buggy
    # TODO: Possible to merge both diffeq and soleq logic.
    def _calcDiffEq(self, global_timeValues, local_timeValues, model_id, index):

        c_val = self.getContValues()

        var_list = self.intervalsVariables()
        interval_list = []


        i_val = []
        for var in range(len(var_list[index])):
            key = var_list[index][var]
            i_val.append(c_val[str(key)][index][0])
            self.mode_module[model_id].getFlow().var_dict[key] = c_val[str(key)][index][0]

        res = odeint(lambda z, t: self.mode_module[model_id].getFlow().exp2exp(), i_val, local_timeValues[index])
        global_newT = global_timeValues[index].tolist()



        # split by variables

        for el in range(len(var_list[index])):
            interval_dict = dict()
            tmp_res = []
            for i, e in enumerate(res):
                # this line makes point pair. For example, below lines will makes
                # pair { "x": 0.0, "y": 20.0 }. "global_newT[i]" is correspond to x value and
                # "e[el]" is correspond to y value in this case.
                pair = dict()
                pair["x"] = global_newT[i]
                pair["y"] = e[el]
                tmp_res.append(pair)
            interval_dict["name"] = var_list[index][el]
            interval_dict["intIndex"] = index
            interval_dict["points"] = tmp_res
            interval_list.append(interval_dict)

#         print("calcDIffEq")
#         print(interval_dict)
        return interval_list, global_newT

    def calcEq(self, global_timeValues, local_timeValues):


        # get total model id
        model_id = self.getModelIdList()

        # Get unique solEq model id list
        solEq_dict = []
        diffEq_dict = []
        for i, ids in enumerate(model_id):
            if self.mode_module[ids].getFlow().type == "sol":
                # check if it is in the list
                tmp = dict()
                tmp["interval"] = i
                tmp["model_id"] = ids
                solEq_dict.append(tmp)

            elif self.mode_module[ids].getFlow().type == "diff":
                tmp = dict()
                tmp["interval"] = i
                tmp["model_id"] = ids
                diffEq_dict.append(tmp)


#         print("Sol eq dict")
#         print(solEq_dict)
#
#         print("Diff eq dict")
#         print(diffEq_dict)

        res = []
        time_list = []

        for elem in solEq_dict:
            elem["data"], elem["time"] = self._calcSolEq(global_timeValues, local_timeValues, elem["model_id"], elem["interval"])

        # TODO: need to add diffEq part..... down here!


        for elem in diffEq_dict:
            elem["data"], elem["time"] = self._calcDiffEq(global_timeValues, local_timeValues, elem["model_id"], elem["interval"])

        for i in range(len(model_id)):
            for elem in solEq_dict:
                if elem["interval"] == i :
                    if 'data' in elem.keys():
                        res += elem["data"]
                    if 'time' in elem.keys():
                        time_dict = dict()
                        time_dict["intIndex"] = i

                        elem_time_pair = []
                        elem_time_pair.append(elem["time"][0])
                        elem_time_pair.append(elem["time"][len(elem["time"])-1])
                        time_dict["range"] = elem_time_pair
                        time_dict["data"] = elem["time"]
                        time_list.append(time_dict)
            for elem in diffEq_dict:
                if elem["interval"] == i:
                    if 'data' in elem.keys():
                        res += elem["data"]
                    if 'time' in elem.keys():
                        time_dict = dict()
                        time_dict["intIndex"] = i

                        elem_time_pair = []
                        elem_time_pair.append(elem["time"][0])
                        elem_time_pair.append(elem["time"][len(elem["time"])-1])
                        time_dict["range"] = elem_time_pair
                        time_dict["data"] = elem["time"]
                        time_list.append(time_dict)
        return res, time_list

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
            #print("visualize start")
            #print(self.getModelIdList())
            '''
                if solution equation exists: 
                checking it via sol_l's length,
                first, it is parsing sol_l by key and value. (for k in sol_l line)
                second, k is variable name of dic and { 'x1' : [ x1 = ..., x1 = .... , ... ] , 'x2' : ... }
            '''

            global_t = self.getNumpyGlobalTimeValues()
            result = list()
            if self.model is not None:
                for i in range(self.bound + 1):
                    declares = self.model.decls()
                    for k in declares:
                        if "time" + str(i) == k.name():
                            result.append(float(self.model[k].as_decimal(6).replace("?", "")))

            print(result)

            local_t = self.getNumpyLocalTimeValues()


            outer2 = dict()

            gmid, _ = self.getModeDeclWithModelID()

            #outer2['data'] = self.calcEq(global_t, local_t)

            outer2['variable'] = self.getVarsId()
            outer2['interval'], outer2["intervalInfo"] = self.calcEq(global_t, local_t)
            outer2['prop'] = self.getProposition()
            outer2['mode'] = gmid
            #outer2['mode'] = self.getModesId()
            #outer2['mode_t'] = self.getModeDecl()
            print(outer2["intervalInfo"])

            import json
            print("New filename: " + "../visualize/src/DataDir/"+self._stackID+".json")
            f = open(("../visualize/src/DataDir/"+self._stackID+".json"), "w")
            json.dump(outer2, f)
            f.close()

        except Exception as ex:
            print('Nothing to draw!', str(ex))
