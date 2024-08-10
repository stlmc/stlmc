import os
import platform
import asyncio
import random
from functools import singledispatch
from typing import Dict, List

from ..constraints.constraints import *
from ..constraints.operations import get_vars, substitution_zero2t, substitution, clause, get_max_bound
from ..exception.exception import NotSupportedError
from ..objects.model import StlMC
from ..solver.abstract_solver import SMTSolver, ParallelSMTSolver
from ..solver.assignment import Assignment
from ..tree.operations import size_of_tree
from ..util.logger import Logger


class DrealAssignment(Assignment):
    def __init__(self, _dreal_model):
        self._dreal_model = _dreal_model

    @staticmethod
    def _sum(real_values: List[RealVal]):
        sum_list = list()
        for i, rv in enumerate(real_values):
            if i == 0:
                sum_list.append(rv)
            else:
                rv_prev = real_values[i - 1]
                sum_value = float(rv_prev.value) + float(rv.value)
                sum_list.append(RealVal(str(sum_value)))
        return sum_list

    @staticmethod
    def _duration_dict2_time_dict(duration_dict: Dict[Real, RealVal]):
        time_str = "time"
        ordered_duration_keys = sorted(list(duration_dict.keys()), key=lambda v: int(v.id[len(time_str) + 1:]))
        ordered_duration_values = list()

        for time_var in ordered_duration_keys:
            ordered_duration_values.append(duration_dict[time_var])

        time_dict: Dict[Real, RealVal] = dict()

        ordered_duration_values = DrealAssignment._sum(ordered_duration_values)
        for cur_index, time_val in enumerate(ordered_duration_values):
            time_dict[Real("tau_{}".format(cur_index + 1))] = time_val

        return time_dict

    # solver_model_to_generalized_model
    def get_assignments(self):
        new_dict = dict()
        duration_dict = dict()
        for e in self._dreal_model:
            # filter any messages not related to assignment
            if ":" in e and "=" in e:
                [var_decl, value] = e.split("=")
                [var_name, var_type] = var_decl.split(":")
                var_name = var_name.replace(" ", "")
                if "Bool" in var_type:
                    val = ""
                    if "true" in value:
                        val = "True"
                    elif "false" in value:
                        val = "False"
                    else:
                        raise NotSupportedError("cannot make dreal assignment")
                    new_dict[Bool(var_name)] = BoolVal(val)
                else:
                    # assume that dreal only returns real
                    [lower_bound, upper_bound] = str(value).replace("[", "").replace("]", "").split(",")
                    # we get midpoint
                    val_float = (float(lower_bound) + float(upper_bound)) / 2
                    val = str(format(val_float, "f"))
                    new_dict[Real(var_name)] = RealVal(val)

        time_dict = DrealAssignment._duration_dict2_time_dict(duration_dict)
        new_dict.update(time_dict)
        return new_dict

    def eval(self, const):
        pass


class newDRealSolver(SMTSolver):
    def __init__(self):
        SMTSolver.__init__(self)
        self._dreal_model = None
        self.file_name = ""
        self.stl_model = None

    def set_logic(self, logic_name: str):
        pass

    def set_time_bound(self, time_bound: float):
        pass

    async def _run(self, consts, logic):
        try:
            return await asyncio.wait_for(self._dreal_check_sat(consts, logic), timeout=100000000.0)
        except asyncio.TimeoutError:
            print('timeout!')

    def set_file_name(self, name):
        self.file_name = name

    def dreal_check_sat(self, consts, stl_model):
        return asyncio.run(self._run(consts, stl_model))

    async def _dreal_check_sat(self, consts, logic):
        assert self.logger is not None and isinstance(self.stl_model, StlMC)
        logger = self.logger
        dreal_section = self.config.get_section("dreal")
        common_section = self.config.get_section("common")
        ode_step = dreal_section.get_value("ode-step")
        ode_order = dreal_section.get_value("ode-order")
        time_horizon = common_section.get_value("time-horizon")
        time_bound = float(common_section.get_value("time-bound"))
        bound = int(common_section.get_value("bound"))
        exec_path = dreal_section.get_value("executable-path")

        decls = list()
        for b in range(bound + 1):
            for mv in self.stl_model.mode_var_dict:
                if mv == "to":
                    continue

                rv_type = self.stl_model.mode_var_dict[mv].type
                v_type = "{}{}".format(rv_type[0].upper(), rv_type[1:])
                decls.append("(declare-fun {}_{} () {})".format(mv, b, v_type))

            for mv in self.stl_model.range_dict:
                assert isinstance(mv, Variable)
                v_type = "{}{}".format(mv.type[0].upper(), mv.type[1:])
                _, le, re, _ = self.stl_model.range_dict[mv]
                decls.append("(declare-fun {} () {} [{}, {}])".format(mv.id, v_type, le, re))
                decls.append("(declare-fun {}_{}_0 () {} [{}, {}])".format(mv.id, b, v_type, le, re))
                decls.append("(declare-fun {}_{}_t () {} [{}, {}])".format(mv.id, b, v_type, le, re))

            decls.append("(declare-fun time_{} () Real [0.0, {}])".format(b, time_horizon))

        for m_ind, m in enumerate(self.stl_model.modules):
            flow = m["flow"]
            flows = list(zip(flow.vars, flow.exps))
            df = list()

            for x, y in flows:
                df.append("(= d/dt[{}] {})".format(dreal_obj(x), dreal_obj(y)))
            decls.append("(define-ode flow_{} ({}))".format(m_ind, " ".join(df)))

        smt_b = "(assert {})".format(dreal_obj(consts))
        t_c = "(assert (<= (+ {}) {}))".format(" ".join(["time_{}".format(b) for b in range(bound + 1)]), time_bound)

        smt_bb = "(set-logic QF_NRA_ODE)\n{}\n{}\n{}\n(check-sat)\n(exit)".format("\n".join(decls), smt_b, t_c)

        str_file_name = "dreal_model" + str(random.random())
        # print(str_file_name)
        with open(str_file_name + ".smt2", 'w') as model_file:
            model_file.write(smt_bb)

        model_file_name = "{}.smt2".format(str_file_name)
        proc = await asyncio.create_subprocess_exec(
            exec_path, model_file_name,
            # "--ode-order", ode_order,
            "--short_sat",
            # "--delta_heuristic",
            # "--sat-prep-bool", "--ode-cache", "--ode-parallel", "--ode-sampling", "--ode-step", ode_step,
            "--model",
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE)

        logger.reset_timer()
        logger.start_timer("solving timer")
        stdout, stderr = await proc.communicate()
        logger.stop_timer("solving timer")
        self.set_time("solving timer", logger.get_duration_time("solving timer"))
        stdout_str = stdout.decode()[len("Solution:\n"):-1]
        stderr_str = stderr.decode()
        output_str = "{}\n{}".format(stdout_str, stderr_str)
        # print(f'[exited with {proc.returncode}]')
        # if stdout:
        #     print(f'[stdout]\n{stdout.decode()}')
        # if stderr:
        #     print(f'[stderr]\n{stderr.decode()}')

        if os.path.isfile(model_file_name):
           os.remove(model_file_name)

        self.stl_model = None
        if "currentMode" in output_str:
            result = "False"
            cont_var_list = stdout_str.split("\n")
            bool_var_list = stderr_str.split("\n")

            result_model = list()
            result_model.extend(cont_var_list)
            result_model.extend(bool_var_list)

            result_model.remove("")
            return result, result_model
        elif "unsat" in stdout.decode():
            return "True", None
        else:
            return "Unknown", None
            # raise NotSupportedError("dreal error")

    def solve(self, all_consts=None, info_dict=None, boolean_abstract=None):
        size = size_of_tree(all_consts)
        # abuse argument
        assert isinstance(self.stl_model, StlMC)
        result, self._dreal_model = self.dreal_check_sat(all_consts, "")
        return result, size

    def set_stl_model(self, stl_model: StlMC):
        self.stl_model = stl_model

    def make_assignment(self):
        return DrealAssignment(self._dreal_model)

    def clear(self):
        pass

    def simplify(self, consts):
        pass

    def substitution(self, const, *dicts):
        pass

    def add(self, const):
        pass


def check_os():
    return platform.platform()


@singledispatch
def dreal_obj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@dreal_obj.register(Constant)
def _(const: Constant):
    return str(const.value).lower()


@dreal_obj.register(Variable)
def _(const: Variable):
    return str(const.id)


@dreal_obj.register(Binary)
def _(const: Binary):
    # binary = [">=", ">", "<=", "<", "=", "+", "-", "*", "/", "^"]

    x = dreal_obj(const.left)
    y = dreal_obj(const.right)

    if isinstance(const, Neq):
        return "(not (= {} {}))".format(x, y)

    return "({} {} {})".format(const._op_str, x, y)


@dreal_obj.register(Unary)
def _(const: Unary):
    unary = ["sqrt", "sin", "cos", "arcsin", "arccos"]

    x = dreal_obj(const.child)
    if isinstance(const, Neg):
        return "(- 0 {})".format(x)

    if isinstance(const, Tan):
        return "(/ (sin {}) (cos {}))".format(x, x)

    if isinstance(const, Arctan):
        return "(/ (cos {}) (sin {}))".format(x, x)

    return "({} {})".format(const._op_str, x)


@dreal_obj.register(Multinary)
def _(const: Multinary):
    if len(const.children) > 1:
        return "({} {})".format(const._op_str, " ".join([dreal_obj(c) for c in const.children]))
    elif len(const.children) < 1:
        return "true"
    else:
        return dreal_obj(const.children[0])


@dreal_obj.register(Integral)
def _(const: Integral):
    s = const.end_vector[0].id.find("_")
    e = const.end_vector[0].id.rfind("_")

    bound = const.end_vector[0].id[s + 1:e]

    e_v = [dreal_obj(ev) for ev in const.end_vector]
    s_v = [dreal_obj(sv) for sv in const.start_vector]
    cm = int(const.current_mode_number)

    return "(= [{}] (integral 0. time_{} [{}] flow_{}))".format(" ".join(e_v), bound, " ".join(s_v), cm)


@dreal_obj.register(Forall)
def _(const: Forall):
    bound = get_max_bound(const.const)
    return "(forall_t {} [0 time_{}] ({}))".format(const.current_mode_number, bound, dreal_obj(const.const))
