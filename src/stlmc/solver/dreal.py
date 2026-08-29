import os
import platform
import subprocess
import tempfile
import threading
import time
from functools import singledispatch
from typing import Dict, List

from ..constraints.constraints import *
from ..constraints.operations import (
    clause, get_max_bound, get_vars, reduce_not, reverse_inequality,
    substitution, substitution_zero2t,
)
from ..constraints.translation import make_dynamics_consts, make_forall_consts
from ..exceptions import NotSupportedError
from ..solver.abstract_solver import (
    JobSolver, SolveResult, SolverJob,
)
from ..solver.assignment import Assignment
from ..solver.dreal_utils import get_dreal_solver_args
from ..utils.smt2_output import is_enabled, write_smt2
from ..constraints.operations import size_of_tree


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

class dRealSolver(JobSolver):
    def __init__(self, config=None):
        JobSolver.__init__(self, config)
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
                if isinstance(i.dynamics, Function):
                    # Closed-form dynamics are algebraic endpoint equations,
                    # not ODE right-hand sides.
                    continue
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

        # add_reset_cond() references every boundary tau, even when an
        # intermediate tau does not otherwise occur in const.  Declare the
        # complete sequence instead of only the tau variables returned by
        # get_vars(const).
        for ki in range(0, max_bound + 2):
            declare_list.append(
                "(declare-fun tau_{} () Real [0, {}])".format(ki, time_bound)
            )

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

    @staticmethod
    def _smt2_text(declares, results, reset_dreal):
        lines = ["(set-logic QF_NRA_ODE)", *declares]
        lines.append("(assert (and{}))".format(
            "".join(" " + result for result in results)
        ))
        lines.append("(assert (and{}))".format(
            "".join(" " + reset for reset in reset_dreal)
        ))
        lines.extend(["(check-sat)", "(exit)"])
        return "\n".join(lines) + "\n"

    def _solver_input(self, content, query_name):
        if is_enabled(self.config):
            path = write_smt2(
                self.config, "dreal", query_name, content
            )
            return [path], None
        fd, path = tempfile.mkstemp(prefix="stlmc-dreal-", suffix=".smt2")
        os.close(fd)
        try:
            with open(path, "w") as smt2_file:
                smt2_file.write(content)
        except Exception:
            os.unlink(path)
            raise
        return [path], path

    def _prepare_solver_command(self, const, query_name):
        dreal_section = self.config.get_section("dreal")
        common_section = self.config.get_section("common")
        time_horizon = float(common_section.get_value("time-horizon"))
        time_bound = float(common_section.get_value("time-bound"))

        declares, bound = self.get_declared_variables(
            const, time_horizon, time_bound
        )
        results = [drealObj(const)]
        reset_dreal = [drealObj(item) for item in self.add_reset_cond(bound)]
        input_args, cleanup_path = self._solver_input(
            self._smt2_text(declares, results, reset_dreal), query_name
        )
        command = [
            dreal_section.get_value("executable-path"),
            *input_args,
            *get_dreal_solver_args(dreal_section),
            "--short_sat",
            "--model",
        ]
        return command, cleanup_path

    @staticmethod
    def _parse_solver_output(returncode, stdout, stderr):
        stdout_text = stdout.decode(errors="replace")
        stderr_text = stderr.decode(errors="replace")
        error_message = None
        if returncode != 0:
            result = "Unknown"
            error_message = "dReal exited with {}: {}".format(
                returncode, stderr_text.strip()
            )
        elif stdout_text.startswith("Solution:\n"):
            result = "False"
        elif "unsat" in stdout_text:
            result = "True"
        else:
            result = "Unknown"
            error_message = "unrecognized dReal output: {}".format(
                (stdout_text + "\n" + stderr_text).strip()
            )

        model_text = (
            stdout_text[len("Solution:\n"):]
            if stdout_text.startswith("Solution:\n") else ""
        )
        model_lines = [
            line for line in (model_text + "\n" + stderr_text).splitlines()
            if line
        ]
        return SolveResult(
            result, DrealAssignment(model_lines), error=error_message
        )

    @staticmethod
    def _cleanup_solver_input(path):
        if path is None:
            return
        for generated_path in (path, path + ".model"):
            try:
                os.unlink(generated_path)
            except FileNotFoundError:
                pass

    def submit(self, const, on_complete=None, query_name=""):
        job = SolverJob(on_complete)
        formula_size = size_of_tree(const)
        command, cleanup_path = self._prepare_solver_command(const, query_name)
        parallel_s_time = time.monotonic()
        proc = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=os.name == "posix")
        check_sat_thread = threading.Thread(target=self.parallel_check_sat,
                                            args=(job, proc, parallel_s_time,
                                                  cleanup_path, formula_size))
        check_sat_thread.daemon = True
        job.set_worker(
            proc,
            process_group=os.name == "posix",
            completion_worker=check_sat_thread,
        )
        check_sat_thread.start()

        return job

    def parallel_check_sat(self, job, proc: subprocess.Popen,
                           start_time=None, cleanup_path=None, formula_size=0):
        if start_time is None:
            start_time = time.monotonic()
        try:
            stdout, stderr = proc.communicate()
            solve_result = self._parse_solver_output(
                proc.returncode, stdout, stderr
            )
        except Exception as error:
            error_message = "parallel worker error: {}".format(error)
            solve_result = SolveResult(
                "Unknown", DrealAssignment([]), error=error_message
            )
        finally:
            self._cleanup_solver_input(cleanup_path)
            elapsed = time.monotonic() - start_time
            solve_result = SolveResult(
                solve_result.result, solve_result.assignment,
                elapsed, solve_result.error, formula_size,
            )
            job.complete(solve_result)

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
    result = '(asin ' + x + ')'
    return result


@drealObj.register(Arccos)
def _(const):
    x = drealObj(const.child)
    result = '(acos ' + x + ')'
    return result


@drealObj.register(Arctan)
def _(const):
    x = drealObj(const.child)
    result = '(atan ' + x + ')'
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
    if isinstance(const.dynamics, Function):
        return drealObj(make_dynamics_consts(const.dynamics))

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
    if isinstance(const.integral.dynamics, Function):
        bound_str = str(int(const.end_tau.id[4:]) - 1)
        if len(get_vars(const.const)) == 0 or isinstance(const.const, Bool):
            return drealObj(const.const)
        if isinstance(const.const, Not):
            if isinstance(const.const.child, Bool):
                return drealObj(const.const)
            reduced = reduce_not(const.const)
            return drealObj(Forall(
                const.current_mode_number, const.end_tau, const.start_tau,
                reduced, const.integral,
            ))
        if isinstance(const.const, Implies):
            left = Forall(
                const.current_mode_number, const.end_tau, const.start_tau,
                reduce_not(Not(const.const.left)), const.integral,
            )
            right = Forall(
                const.current_mode_number, const.end_tau, const.start_tau,
                const.const.right, const.integral,
            )
            return drealObj(Or([left, right]))
        if isinstance(const.const, (And, Or)):
            children = [
                child if isinstance(child, Bool) else Forall(
                    const.current_mode_number, const.end_tau,
                    const.start_tau, child, const.integral,
                )
                for child in const.const.children
            ]
            return drealObj(const.const.__class__(children))

        op_dict = {Gt: Gt, Geq: Geq, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq}
        expression = Sub(const.const.left, const.const.right)
        normalized = reverse_inequality(
            op_dict[type(const.const)](expression, RealVal("0"))
        )
        algebraic = make_forall_consts(Forall(
            const.current_mode_number, const.end_tau, const.start_tau,
            normalized, const.integral,
        ))
        return drealObj(And([
            Eq(Real("currentMode_" + bound_str),
               RealVal(str(const.current_mode_number))),
            algebraic,
        ]))

    cur_inv = substitution_zero2t(const.const)
    # all bounds are same
    bound = get_max_bound(const.const)
    d_obj = drealObj(cur_inv)
    return "(and (= currentMode_{} {}) (forall_t {} [0 time_{}] ({})))".format(bound, const.current_mode_number,
                                                                               const.current_mode_number + 1, bound,
                                                                               d_obj)
