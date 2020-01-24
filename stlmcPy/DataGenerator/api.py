from yices import *
import z3
import os
from stlmcPy.core.node import *
from stlmcPy.core.model import *
import numpy as np
from scipy.integrate import odeint


class Api:

    @property
    def stackID(self):
        return self._stackID

    # give file name and it will generate stackID
    # this must be invoke after data method called
    @stackID.setter
    def stackID(self, stackID):
        self._stackID = stackID + "_" + self.stl + "_" + str(self.bound)

    @property
    def solver(self):
        return self._solver

    @solver.setter
    def solver(self, solver):
        self._solver = solver

    @property
    def data(self):
        return self._data

    # return {'var_id' : value ,...} dictionary, for yices solver
    def getvarval(self):
        all_terms = self.model.collect_defined_terms()
        var_val = dict()
        for term in all_terms:
            var_val[str(Terms.get_name(term))] = self.model.get_value(term)
        return var_val

    @property
    def result(self):
        return self._result

    @result.setter
    def result(self, res):
        self._result = str(res)

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
        #         for i in range(len(self.modeVar)):
        #            result.append(str(self.modeVar[i].id))
        return result

    # return mode variables id
    def getModesIdDict(self):
        result = {}
        for i in range(len(self.modeVar)):
            result[str(self.modeVar[i].id)] = (list(), str(self.modeVar[i].type))
        return result

    # return mode declaraion to string
    def getModeDeclWithModelID(self):
        total = list()
        idList = list()
        if self.model is not None:
            result = {}
            modeValues = self.getModeValues()

            for i in range(len(self.modeVar)):
                key = self.modeVar[i].id
                subResult = []
                for index in range(len(modeValues[key]) - 1):
                    subResult.append(modeValues[key][index][0])
                result[key] = (subResult, self.modeVar[i].type)

            idList = self.getModeIdList()

            total = list()
            for key in result.keys():
                dictElement = dict()
                dictElement["name"] = key
                dictElement["type"] = result[key][1]
                dictElement["data"] = result[key][0]
                total.append(dictElement)
        return total, idList

    # return (initial, final) pairs for each continuous variable until k bound
    def getContValues(self):
        result = {}
        if self.model is not None:
            for i in range(len(self.contVar)):
                subResult = []
                if self._solver == 'z3':
                    op = {'bool': z3.Bool, 'int': z3.Int, 'real': z3.Real}
                elif self._solver == 'yices':
                    import yices
                    op = {'bool': yices.Types.bool_type(), 'int': yices.Types.int_type(), 'real': yices.Types.real_type()}
                else:
                    raise ValueError("Can't support the given solver, please use z3 or yices solvers")

                for j in range(self.bound + 1):
                    if self._solver == 'z3':
                        initial_var = op[self.contVar[i].type](str(self.contVar[i].id) + "_" + str(j) + "_0")
                        final_var = op[self.contVar[i].type](str(self.contVar[i].id) + "_" + str(j) + "_t")
                        initial_value = float(self.model[initial_var].as_decimal(6).replace("?", ""))
                        final_value = float(self.model[final_var].as_decimal(6).replace("?", ""))
                    elif self._solver == 'yices':
                        var_val = self.getvarval()
                        initial_id = str(self.contVar[i].id) + "_" + str(j) + "_0"
                        final_id = (str(self.contVar[i].id) + "_" + str(j) + "_t")
                        if initial_id in var_val.keys():
                            initial_value = float(var_val[initial_id])
                        if final_id in var_val.keys():
                            final_value = float(var_val[final_id])
                    else:
                        raise ValueError("Can't support the given solver, please use z3 or yices solvers")

                    subResult.append((initial_value, final_value))

                if self._solver == 'z3':
                    final_var = op[self.contVar[i].type](str(self.contVar[i].id) + "_" + str(self.bound + 1) + "_0")
                    if self.model[final_var] is not None:
                        final_value = float(self.model[final_var].as_decimal(6).replace("?", ""))
                elif self._solver == 'yices':
                    final_id = str(self.contVar[i].id) + "_" + str(self.bound + 1) + "_0"
                    if final_id in self.getvarval().keys():
                        final_value = float(self.getvarval()[final_id])
                else:
                    pass

                subResult.append((final_value, final_value))
                result[str(self.contVar[i].id)] = subResult

        return result

    # return (initial, final) pairs for each mode variable until k bound
    def getModeValues(self):
        result = {}
        if self.model is not None:
            for i in range(len(self.modeVar)):
                subResult = []
                if self._solver == 'z3':
                    op = {'bool': z3.Bool, 'int': z3.Int, 'real': z3.Real}
                elif self._solver == 'yices':
                    import yices
                    op = {'bool': yices.Types.bool_type(), 'int': yices.Types.int_type(), 'real': yices.Types.real_type()}
                else:
                    raise ValueError("Can't support the given solver, please use z3 or yices solvers")

                for j in range(self.bound + 2):
                    if self._solver == 'z3':
                        var = op[self.modeVar[i].type](str(self.modeVar[i].id) + "_" + str(j))
                        if self.modeVar[i].type == 'bool':
                            var_value = str(self.model[var])
                        elif self.modeVar[i].type == 'int':
                            var_value = int(str(self.model[var]))
                        else:
                            var_value = float(self.model[var].as_decimal(6).replace("?", ""))
                    elif self._solver == 'yices':
                        var_val = self.getvarval()
                        var = str(self.modeVar[i].id) + "_" + str(j)
                        if self.modeVar[i].type == 'bool':
                            var_value = str(var_val[var])
                        else:
                            var_value = float(var_val[var])
                    subResult.append((var_value, var_value))
                result[str(self.modeVar[i].id)] = subResult
        return result

    # return list of variable point times
    def getTauValues(self):
        result = list()
        if self.model is not None:
            for i in range(self.bound + 1):
                time_value = None
                if self._solver == 'z3':
                    time_var = z3.Real("time" + str(i))
                    if self.model[time_var] is not None:
                        time_value = float(self.model[time_var].as_decimal(6).replace("?", ""))
                elif self._solver == 'yices':
                    all_terms = self.model.collect_defined_terms()
                    var_val = dict()
                    for term in all_terms:
                        var_val[str(Terms.get_name(term))] = self.model.get_value(term)
                    time_id = "time" + str(i)
                    if time_id in var_val.keys():
                        time_value = var_val[time_id]
                else:
                    raise ValueError("Can't support the given solver, please use z3 or yices solvers")

                if time_value is not None:
                    result.append(time_value)
        return result

    # return list of time points
    def getNumpyGlobalTimeValues(self):
        result = self.getTauValues()
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
            else:
                t.append(np.linspace(sum_pre, sum))
        return t

    # return list of interval's time points
    def getNumpyLocalTimeValues(self):
        result = self.getTauValues()

        t = []
        for t_el in range(len(result)):
            t.append(np.linspace(0, result[t_el]))
        return t

    # TODO : change function name to getModeIdList
    def getModeIdList(self):
        result = []
        if self.model is not None:
            for i in range(self.bound + 2):
                modeId_value = None
                if self._solver == 'z3':
                    modeId_var = z3.Real("currentMode_" + str(i))
                    if self.model[modeId_var] is not None:
                        modeId_value = int(self.model[modeId_var].as_decimal(6).replace("?", ""))
                elif self._solver == 'yices':
                    var_val = self.getvarval()
                    modeId_var = "currentMode_" + str(i)
                    if modeId_var in var_val.keys():
                        modeId_value = int(var_val[modeId_var])
                else:
                    raise ValueError("Can't support the given solver, please use z3 or yices solvers")
                if modeId_value is not None:
                    result.append(modeId_value)
        return result

    # return (var, mod, both)
    # return variable only, mode variable only, both initial value
    def getSolEqInitialValue(self):
        c_val = self.getContValues()

        c_initial = dict()
        m_initial = dict()
        initial_val = dict()

        # add mode var
        if self.model is not None:
            for i in range(len(self.modeVar)):
                total = self.getModeValues()
                subResult = [i[0] for i in total[str(self.modeVar[i].id)]]
                m_initial[str(self.modeVar[i].id)] = subResult
                initial_val[str(self.modeVar[i].id)] = subResult

        for i in c_val.keys():
            subResult = []
            for j in range(self.bound + 2):
                subResult.append(c_val[i][j][0])
            c_initial[i] = subResult
            initial_val[i] = subResult

        return c_initial, m_initial, initial_val

    def getSol(self):
        ode_l = self.getModeIdList()
        initial_val, _, _ = self.getSolEqInitialValue()
        solutionBound = dict()
        for i in initial_val.keys():
            solutionList = list()
            for j in range(len(ode_l)):
                modexps = self.mode_module[ode_l[j]].getFlow().exp()
                for k in range(len(modexps)):
                    if modexps[k].getVarId() == i:
                        subResult = modexps[k]
                        solutionList.append(subResult)
                        break
            solutionBound[i] = solutionList
        # solutionBound : Dict of variables and value of SolEq type object list
        # "x1": [sol_eq1, sol_eq2, ...]
        return solutionBound

    def getProposition(self):
        result = []
        if self.model is not None:
            midList = []
            formulaTerms = []
            for termElem in self.stl.split():
                formulaTerms.append(termElem.replace("(", "").replace(")", ""))
            for modevar in self.modeVar:
                if modevar.id in formulaTerms:
                    midList.append(modevar)

            if len(midList) > 0:
                for mode in midList:
                    subResult = []
                    for j in range(self.bound + 2):
                        if self._solver == 'z3':
                            propVar = z3.Bool(mode.id + "_" + str(j))
                            if self.model[propVar] is not None:
                                subResult.append(str(self.model[propVar]))
                        elif self._solver == 'yices':
                            var_val = self.getvarval()
                            propVar = mode.id + "_" + str(j)
                            if propVar in var_val.keys():
                                subResult.append(str(var_val[propVar]))
                        else:
                            raise ValueError("Can't support the given solver, please use z3 or yices solvers")
                    resultVal = dict()
                    resultVal["name"] = str(mode.id)
                    resultVal["actual"] = str(mode)
                    resultVal["data"] = subResult
                    result.append(resultVal)
            for i in range(len(self.props)):
                subResult = []
                propID = str(self.props[i].getId())
                idCheck = (propID in self.stl) or ("newPropDecl_" in propID)
                for j in range(self.bound + 2):
                    if idCheck:
                        if self._solver == 'z3':
                            propVar = z3.Bool(propID + "_" + str(j))
                            if self.model[propVar] is not None:
                                subResult.append(str(self.model[propVar]))

                        elif self._solver == 'yices':
                            var_val = self.getvarval()
                            propVar = propID + "_" + str(j)
                            if propVar in var_val.keys():
                                subResult.append(str(var_val[propVar]))
                        else:
                            raise ValueError("Can't support the given solver, please use z3 or yices solvers")

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
        _, only_mod, sol_init_list = self.getSolEqInitialValue()
        sol_l = self.getSol()
        interval_list = []

        sol_l_list = list(sol_l.keys())

        # k is variable name of dic
        # { 'x1' : [ x1 = ..., x1 = .... , ... ] , 'x2' : ... }
        for k in sol_l:
            interval_dict = dict()
            tmp_res = []

            for vv in only_mod:
                self.mode_module[model_id].getFlow().var_dict[vv] = sol_init_list[vv][index]

            self.mode_module[model_id].getFlow().var_dict[k] = sol_init_list[k][index]
            for const in self.subvars:
                self.mode_module[model_id].getFlow().var_dict[const] = float(str(self.subvars[const]))

            global_newT = global_timeValues[index].tolist()
            local_newT = local_timeValues[index].tolist()
            # modify this to use given initial value and time pairs
            for i in range(len(local_newT)):
                self.mode_module[model_id].getFlow().var_dict["time"] = local_newT[i]
                # this line makes point pair. For example, below lines will makes
                # pair { "x": 0.0, "y": 20.0 }. "global_newT[i]" is correspond to x value and
                # "self.mode_module[model_id].getFlow().exp2exp()" is correspond to y value
                # but for some reason "self.mode_module[model_id].getFlow().exp2exp()" itself
                # contains [value]. So we need to remove list before putting it inside tmp dictionary.
                # That is why we use "self.mode_module[model_id].getFlow().exp2exp()[k]" instead.
                tmp = dict()
                tmp["x"] = global_newT[i]
                tmp["y"] = self.mode_module[model_id].getFlow().exp2exp()[sol_l_list.index(k)]
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
        m_val = self.getModeValues()

        var_list = self.intervalsVariables()
        _, only_mod, sol_init_list = self.getSolEqInitialValue()
        interval_list = []

        i_val = []
        for var in range(len(var_list[index])):
            key = var_list[index][var]
            i_val.append(c_val[str(key)][index][0])
            for vv in only_mod:
                self.mode_module[model_id].getFlow().var_dict[vv] = sol_init_list[vv][index]
            self.mode_module[model_id].getFlow().var_dict[key] = c_val[str(key)][index][0]
            for k in self.subvars:
                self.mode_module[model_id].getFlow().var_dict[k] = float(str(self.subvars[k]))

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

        return interval_list, global_newT

    def calcEq(self, global_timeValues, local_timeValues):
        # get total model id
        model_id = self.getModeIdList()

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

        res = []
        time_list = []

        for elem in solEq_dict:
            elem["data"], elem["time"] = self._calcSolEq(global_timeValues, local_timeValues, elem["model_id"],
                                                         elem["interval"])

        # TODO: need to add diffEq part..... down here!

        for elem in diffEq_dict:
            elem["data"], elem["time"] = self._calcDiffEq(global_timeValues, local_timeValues, elem["model_id"],
                                                          elem["interval"])

        for i in range(len(model_id)):
            for elem in solEq_dict:
                if elem["interval"] == i:
                    if 'data' in elem.keys():
                        res += elem["data"]
                    if 'time' in elem.keys():
                        time_dict = dict()
                        time_dict["intIndex"] = i

                        elem_time_pair = []
                        elem_time_pair.append(elem["time"][0])
                        elem_time_pair.append(elem["time"][len(elem["time"]) - 1])
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
                        elem_time_pair.append(elem["time"][len(elem["time"]) - 1])
                        time_dict["range"] = elem_time_pair
                        time_dict["data"] = elem["time"]
                        time_list.append(time_dict)

        return res, time_list


    # get intervals variable list
    # only gets contVar that is LHS of an equation
    def intervalsVariables(self):
        model_id = self.getModeIdList()
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

            '''
                if solution equation exists: 
                checking it via sol_l's length,
                first, it is parsing sol_l by key and value. (for k in sol_l line)
                second, k is variable name of dic and { 'x1' : [ x1 = ..., x1 = .... , ... ] , 'x2' : ... }
            '''

            global_t = self.getNumpyGlobalTimeValues()
            result = self.getTauValues()

            local_t = self.getNumpyLocalTimeValues()

            outer2 = dict()

            gmid, _ = self.getModeDeclWithModelID()

            outer2['variable'] = self.getVarsId()
            outer2['interval'], outer2["intervalInfo"] = self.calcEq(global_t, local_t)
            outer2['prop'] = self.getProposition()
            outer2['mode'] = gmid

            try:
                if not (os.path.isdir("./DataDir")):
                    os.makedirs(os.path.join("./DataDir"))
            except OSError as e:
                if e.errno != errno.EEXIST:
                    raise ValueError("Failed to create directory!!!!!")

            if self._result == "False":
                import json
                f = open(("./DataDir/" + self._stackID + "_" + self._solver + ".cep"), "w")
                json.dump(outer2, f)
                f.close()
                print("New filename: " + "./DataDir/" + self._stackID + "_" + self._solver + ".cep")

        except Exception as ex:
            print("Error occured, {}".format(ex))
