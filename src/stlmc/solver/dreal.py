import os
import platform
import asyncio
import random
import subprocess
import threading
import time
from functools import singledispatch
from queue import Queue, Empty
from typing import Dict, List

from ..constraints.constraints import *
from ..constraints.operations import get_vars, substitution_zero2t, substitution, clause, get_max_bound
from ..exception.exception import NotSupportedError
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


class dRealSolver(ParallelSMTSolver):
    def __init__(self):
        SMTSolver.__init__(self)
        self._dreal_model = None
        self._cache = list()
        self._cache_raw = list()
        self._logic_list = ["QF_NRA_ODE"]
        self._logic = "QF_NRA_ODE"
        self._time_bound = None
        self.stdout_msg = Queue()
        self.stderr_msg = Queue()
        self.done = False
        self._parallel_result = None
        self._parallel_model = None
        self._parallel_s_time = 0.0
        self._parallel_e_time = 0.0
        self.file_name = ""

    def set_logic(self, logic_name: str):
        self._logic = (logic_name.upper() if logic_name.upper() in self._logic_list else 'QF_NRA_ODE')

    def set_time_bound(self, time_bound: float):
        pass

    def add_reset_cond(self, bound: int):
        result = list()
        result.append(Eq(Real("tau_" + str(0)), Real("g@clock_0_0")))
        for i in range(1, bound + 2):
            result.append(Eq(Real("tau_" + str(i)), Real("g@clock_" + str(i - 1) + "_t")))
            if i < bound + 1:
                result.append(Eq(Real("g@clock_" + str(i) + "_0"), Real("g@clock_" + str(i - 1) + "_t")))
        return result

    def get_declared_variables(self, const, time_horizon: float, time_bound: float):
        declare_list = list()
        all_vars = set()
        clause_set = clause(const)
        variable_range = list()
        # for i in self._cache:
        #     clause_set = clause_set.union(clause(i))

        for c in clause_set:
            possible_range = isinstance(c, Eq) or isinstance(c, Lt) or isinstance(c, Leq) or isinstance(c,
                                                                                                        Gt) or isinstance(
                c, Geq)
            if possible_range:
                if c.is_range:
                    variable_range.append(c)

        continuous_vars = set()
        time_vars = set()
        clock_vars = set()
        discrete_vars = set()
        integrals = set()
        consider_mode = set()
        global_clock = Real("g@clock")
        clock_vars.add(global_clock)
        # for i in consts:
        #     all_vars = all_vars.union(get_vars(i))
        all_vars = get_vars(const)
        for i in all_vars:
            if isinstance(i, Real) and i.id.rfind("_") != i.id.find("_"):
                continuous_vars.add(Real(i.id[0:i.id.find("_")]))
            elif isinstance(i, Real) and "tau_" in i.id:
                time_vars.add(i)
            elif isinstance(i, Real) and "time_" in i.id:
                pass
            elif isinstance(i, Integral):
                if not i.current_mode_number in consider_mode:
                    consider_mode.add(i.current_mode_number)
                    arb_end = i.end_vector[0].id
                    arb_start = i.start_vector[0].id
                    e_ind = arb_end[arb_end.find("_"):]
                    s_ind = arb_start[arb_start.find("_"):]
                    gt_end = Real("g@clock" + e_ind)
                    gt_start = Real("g@clock" + s_ind)
                    new_start_vec = i.start_vector.copy()
                    new_end_vec = i.end_vector.copy()
                    new_start_vec.append(gt_start)
                    new_end_vec.append(gt_end)

                    new_ode_var = i.dynamics.vars.copy()
                    new_ode_val = i.dynamics.exps.copy()
                    new_ode_var.append(Real(gt_start.id + "_t"))
                    new_ode_val.append(RealVal("1"))

                    new_ode = Ode(new_ode_var, new_ode_val)
                    new_integral = Integral(i.current_mode_number, new_end_vec, new_start_vec, new_ode)
                    # integrals.add(i)
                    integrals.add(new_integral)
            else:
                discrete_vars.add(i)

        var_range_dict = dict()
        clock_range_dict = dict()

        for i in continuous_vars:
            var_range_dict[i.id] = ("[", -99999, 99999, "]")
        for i in time_vars:
            var_range_dict[i.id] = ("[", 0, time_bound, "]")
        for i in clock_vars:
            clock_range_dict[i.id] = ("[", 0, time_bound, "]")
        for i in variable_range:
            if i.left.id.find("_") == i.left.id.rfind("_"):
                str_id = i.left.id
            else:
                str_id = i.left.id[0:i.left.id.find("_")]
            (left_strict, lower, upper, right_strict) = var_range_dict[str_id]
            if isinstance(i, Lt) or isinstance(i, Leq):
                upper = float(i.right.value)
                if isinstance(i, Lt):
                    left_strict = "("
            else:
                lower = float(i.right.value)
                if isinstance(i, Gt):
                    right_strict = ")"
            var_range_dict[str_id] = (left_strict, lower, upper, right_strict)

        # get max bound
        max_bound = -1
        for i in time_vars:
            if "tau_" in i.id:
                cur_bound = int(i.id[i.id.find("_") + 1:])
                if cur_bound > max_bound:
                    max_bound = cur_bound - 1

        for ki in range(0, max_bound + 1):
            time_range = "(declare-fun time_{} () Real [0, {}])".format(ki, time_horizon)
            declare_list.append(time_range)

        # continuous variables declaration
        for i in var_range_dict:
            (left_strict, lower, upper, right_strict) = var_range_dict[i]
            range_str = "[{}, {}]".format(lower, upper)
            if not ("tau_" in i):
                sub_result = "(declare-fun " + i + " () Real "
                sub_result = sub_result + range_str + ")"
                declare_list.append(sub_result)
                for j in range(max_bound + 1):
                    sub_result = "(declare-fun " + i + "_" + str(j) + "_0 () Real " + range_str + ")"
                    declare_list.append(sub_result)
                    sub_result = "(declare-fun " + i + "_" + str(j) + "_t () Real " + range_str + ")"
                    declare_list.append(sub_result)
            elif "tau" in i:
                sub_result = "(declare-fun " + i + " () Real "
                sub_result = sub_result + range_str + ")"
                declare_list.append(sub_result)

        # time variables declaration
        for i in clock_range_dict:
            (left_strict, lower, upper, right_strict) = clock_range_dict[i]
            range_str = "[{}, {}]".format(lower, upper)
            declare_list.append("(declare-fun " + i + " () Real " + range_str + ")")

        for ki in range(0, max_bound + 1):
            for i in clock_range_dict:
                (left_strict, lower, upper, right_strict) = clock_range_dict[i]
                range_str = "[{}, {}]".format(lower, upper)
                declare_list.append("(declare-fun " + i + "_" + str(ki) + "_0 () Real " + range_str + ")")
                declare_list.append("(declare-fun " + i + "_" + str(ki) + "_t () Real " + range_str + ")")

        # discrete variables declaration
        for i in discrete_vars:
            op = {Real: "Real", Bool: "Bool", Int: "Int"}
            type_str = op[type(i)]
            if "currentMode_" in i.id:
                type_str = "Int"
            sub_result = "(declare-fun " + i.id + " () " + type_str + ")"
            sub_result = sub_result.replace("{", "@")
            sub_result = sub_result.replace("}", "@")
            sub_result = sub_result.replace(",", "@")
            declare_list.append(sub_result)

        # ode declaration
        sub_dict = dict()
        for i in var_range_dict:
            for j in range(max_bound + 1):
                sub_dict[Real(i + "_" + str(j) + "_0")] = Real(i)
                sub_dict[Real(i + "_" + str(j) + "_t")] = Real(i)

        for cur_integral in integrals:
            sub_result = "(define-ode flow_" + str(int(cur_integral.current_mode_number) + 1) + " ("
            for i in range(len(cur_integral.dynamics.exps)):
                cur_id = cur_integral.end_vector[i].id[0:cur_integral.end_vector[i].id.find("_")]
                cur_exp = substitution(cur_integral.dynamics.exps[i], sub_dict)
                sub = "(= d/dt[" + cur_id + "] (" + drealObj(cur_exp) + "))"
                sub_result = sub_result + " " + sub
            sub_result = sub_result + "))"
            declare_list.append(sub_result)

        return declare_list, max_bound

    async def _run(self, consts, logic):
        try:
            return await asyncio.wait_for(self._drealcheckSat(consts, logic), timeout=100000000.0)
        except asyncio.TimeoutError:
            print('timeout!')

    @staticmethod
    def enqueue_out(out, queue):
        msg = list()
        for line in iter(out.readline, b''):
            msg.append(line.decode())
        queue.put(msg)
        out.close()

    def set_file_name(self, name):
        self.file_name = name

    def process(self, main_queue: Queue, sema: threading.Semaphore, const):
        dreal_section = self.config.get_section("dreal")
        common_section = self.config.get_section("common")
        ode_step = dreal_section.get_value("ode-step")
        ode_order = dreal_section.get_value("ode-order")
        time_horizon = common_section.get_value("time-horizon")
        time_bound = common_section.get_value("time-bound")
        exec_path = dreal_section.get_value("executable-path")

        declares, bound = self.get_declared_variables(const, float(time_horizon), float(time_bound))
        results = [drealObj(const)]

        reset_add = self.add_reset_cond(bound)

        reset_dreal = list()
        for i in reset_add:
            reset_dreal.append(drealObj(i))

        str_file_name = "dreal_model" + str(random.random())
        if self.file_name == "":
            dir_name = "./dreal_log"
            model_file_name = "{}/{}.smt2".format(dir_name, str_file_name)
        else:
            dir_name = "./dreal_log/{}".format(self.file_name)
            model_file_name = "{}/{}.smt2".format(dir_name, str_file_name)

        if not os.path.exists(dir_name):
            os.makedirs(dir_name)
        with open(model_file_name, 'w') as model_file:
            model_file.write("(set-logic QF_NRA_ODE)\n")
            model_file.write("\n".join(declares))
            model_file.write("\n")
            assertion = "(assert (and"
            for i in results:
                assertion = assertion + " " + i
            assertion = assertion + "))"
            model_file.write(assertion + "\n")
            assertion = "(assert (and"
            for i in reset_dreal:
                assertion = assertion + " " + i
            assertion = assertion + "))"
            model_file.write(assertion + "\n")
            model_file.write("(check-sat)\n")
            model_file.write("(exit)\n")

        self._parallel_s_time = time.time()
        proc = subprocess.Popen(
            [exec_path, model_file_name, "--short_sat", "--model"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)

        check_sat_thread = threading.Thread(target=self.parallel_check_sat, args=(main_queue, sema, proc))
        check_sat_thread.daemon = True
        check_sat_thread.start()

        return proc

    def parallel_check_sat(self, main_queue: Queue, sema: threading.Semaphore, proc: subprocess.Popen):
        stdout, stderr = proc.communicate()
        stdout_str = stdout.decode()[len("Solution:\n"):-1]
        stderr_str = stderr.decode()
        output_str = "{}\n{}".format(stdout_str, stderr_str)
        # print(f'[exited with {proc.returncode}]')
        # if stdout:
        #     print(f'[stdout]\n{stdout.decode()}')
        # if stderr:
        #     print(f'[stderr]\n{stderr.decode()}')

        # if os.path.isfile(model_file_name):
        #    os.remove(model_file_name)

        if "currentMode" in output_str:
            result = "False"
        elif "unsat" in stdout.decode():
            result = "True"
        else:
            result = "Unknown"

        cont_var_list = stdout_str.split("\n")
        bool_var_list = stderr_str.split("\n")

        result_model = list()
        result_model.extend(cont_var_list)
        result_model.extend(bool_var_list)

        result_model.remove("")
        main_queue.put((result, DrealAssignment(result_model), id(proc)))
        sema.release()

    def drealcheckSat(self, consts, logic):
        return asyncio.run(self._run(consts, logic))

    async def _drealcheckSat(self, consts, logic):
        assert self.logger is not None
        logger = self.logger
        dreal_section = self.config.get_section("dreal")
        common_section = self.config.get_section("common")
        ode_step = dreal_section.get_value("ode-step")
        ode_order = dreal_section.get_value("ode-order")
        time_horizon = common_section.get_value("time-horizon")
        time_bound = common_section.get_value("time-bound")
        exec_path = dreal_section.get_value("executable-path")

        declares, bound = self.get_declared_variables(And(consts.copy()), float(time_horizon), float(time_bound))
        results = list()

        for i in consts:
            results.append(drealObj(i))

        reset_add = self.add_reset_cond(bound)

        reset_dreal = list()

        for i in reset_add:
            reset_dreal.append(drealObj(i))

        str_file_name = "dreal_model" + str(random.random())
        with open(str_file_name + ".smt2", 'w') as model_file:
            model_file.write("(set-logic QF_NRA_ODE)\n")
            model_file.write("\n".join(declares))
            model_file.write("\n")
            assertion = "(assert (and"
            for i in results:
                assertion = assertion + " " + i
            assertion = assertion + "))"
            model_file.write(assertion + "\n")
            assertion = "(assert (and"
            for i in reset_dreal:
                assertion = assertion + " " + i
            assertion = assertion + "))"
            model_file.write(assertion + "\n")
            model_file.write("(check-sat)\n")
            model_file.write("(exit)\n")

        model_file_name = "{}.smt2".format(str_file_name)
        proc = await asyncio.create_subprocess_exec(
            exec_path, model_file_name,
            "--short_sat",
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

    def solve(self, all_consts=None, info_dict=None, boolean_abstract=None):
        self._cache.clear()
        if all_consts is not None:
            self._cache.append(all_consts)
            self._cache_raw.append(all_consts)
        size = size_of_tree(And(self._cache_raw))
        result, self._dreal_model = self.drealcheckSat(self._cache, self._logic)
        return result, size

    def make_assignment(self):
        return DrealAssignment(self._dreal_model)

    def clear(self):
        self._cache = list()
        self._cache_raw = list()

    def simplify(self, consts):
        pass

    def substitution(self, const, *dicts):
        pass

    def add(self, const):
        pass


def check_os():
    return platform.platform()


@singledispatch
def drealObj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@drealObj.register(RealVal)
def _(const: RealVal):
    return str(const.value)


@drealObj.register(IntVal)
def _(const: IntVal):
    return str(const.value)


@drealObj.register(BoolVal)
def _(const: BoolVal):
    if const.value == 'True':
        return 'true'
    elif const.value == 'False':
        return 'false'
    else:
        raise NotSupportedError("Z3 solver cannot translate this")


@drealObj.register(Variable)
def _(const: Variable):
    v_id = str(const.id)
    v_id = v_id.replace("{", "@")
    v_id = v_id.replace("}", "@")
    v_id = v_id.replace(",", "@")
    return v_id


@drealObj.register(Geq)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(>= ' + x + ' ' + y + ')'
    return result


@drealObj.register(Gt)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(> ' + x + ' ' + y + ')'
    return result


@drealObj.register(Leq)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(<= ' + x + ' ' + y + ')'
    return result


@drealObj.register(Lt)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(< ' + x + ' ' + y + ')'
    return result


@drealObj.register(Eq)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(= ' + x + ' ' + y + ')'
    return result


@drealObj.register(Neq)
def _(const):
    reduceNot = Not(Eq(const.left, const.right))
    return drealObj(reduceNot)


@drealObj.register(Add)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(+ ' + x + ' ' + y + ')'
    return result


@drealObj.register(Sub)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(- ' + x + ' ' + y + ')'
    return result


@drealObj.register(Pow)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(^ ' + x + ' ' + y + ')'
    return result


@drealObj.register(Mul)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(* ' + x + ' ' + y + ')'
    return result


@drealObj.register(Div)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(/ ' + x + ' ' + y + ')'
    return result


@drealObj.register(Neg)
def _(const):
    x = drealObj(const.child)
    result = '(- ' + str(0) + ' ' + x + ')'
    return result


@drealObj.register(Sqrt)
def _(const):
    x = drealObj(const.child)
    result = '(sqrt ' + x + ')'
    return result


@drealObj.register(Sin)
def _(const):
    x = drealObj(const.child)
    result = '(sin ' + x + ')'
    return result


@drealObj.register(Cos)
def _(const):
    x = drealObj(const.child)
    result = '(cos ' + x + ')'
    return result


@drealObj.register(Tan)
def _(const):
    x = drealObj(const.child)
    result = '(/ (sin ' + x + ') (cos ' + x + '))'
    return result


@drealObj.register(Arcsin)
def _(const):
    x = drealObj(const.child)
    result = '(arcsin ' + x + ')'
    return result


@drealObj.register(Arccos)
def _(const):
    x = drealObj(const.child)
    result = '(arccos ' + x + ')'
    return result


@drealObj.register(Arctan)
def _(const):
    x = drealObj(const.child)
    result = '(/ (cos ' + x + ') (sin ' + x + '))'
    return result


@drealObj.register(And)
def _(const):
    yicesargs = [drealObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(and ' + ' '.join(yicesargs) + ')'
        return result


@drealObj.register(Or)
def _(const):
    yicesargs = [drealObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(or ' + ' '.join(yicesargs) + ')'
        return result


@drealObj.register(Implies)
def _(const):
    x = drealObj(const.left)
    y = drealObj(const.right)
    result = '(=> ' + x + ' ' + y + ')'
    return result


@drealObj.register(Not)
def _(const):
    x = drealObj(const.child)
    result = '(not ' + x + ')'
    return result


@drealObj.register(Integral)
def _(const: Integral):
    s = const.end_vector[0].id.find("_")
    e = const.end_vector[0].id.rfind("_")

    new_end_vector = const.end_vector.copy()
    new_start_vector = const.start_vector.copy()

    bound = const.end_vector[0].id[s + 1:e]

    new_end_vector.append(Real("g@clock_" + str(bound) + "_t"))
    new_start_vector.append(Real("g@clock_" + str(bound) + "_0"))

    setting_end = "(= " + str(new_end_vector).replace(",", "") + " (integral 0. "

    setting_end = setting_end + "time_" + bound + " " + str(new_start_vector).replace(",",
                                                                                      "") + " flow_" + str(
        int(const.current_mode_number) + 1) + "))"

    return setting_end


@drealObj.register(Forall)
def _(const: Forall):
    cur_inv = substitution_zero2t(const.const)
    # all bounds are same
    bound = get_max_bound(const.const)
    d_obj = drealObj(cur_inv)
    return "(and (= currentMode_{} {}) (forall_t {} [0 time_{}] ({})))".format(bound, const.current_mode_number,
                                                                               const.current_mode_number + 1, bound,
                                                                               d_obj)
