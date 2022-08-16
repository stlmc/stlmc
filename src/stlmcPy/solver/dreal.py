import os
import platform
import random
import subprocess
import time

from ..constraints.aux.operations import *
from ..encoding.smt.model.aux import *
from ..encoding.smt.model.stlmc_model import STLmcModel
from ..exception.exception import NotSupportedError
from ..objects.configuration import Configuration
from ..solver.abstract_solver import SMTSolver
from ..solver.assignment import Assignment
from ..util.printer import indented_str


class DrealSolver(SMTSolver):
    def __init__(self, config: Configuration):
        SMTSolver.__init__(self)
        self._cache: List[List[Formula]] = [[]]
        self._config = config
        self._model = None

    def check_sat(self, *assumption, **information):
        cache_const = self._get_cache_const()
        max_bound = int(self._config.get_section("common").get_value("bound"))
        time_horizon = float(self._config.get_section("common").get_value("time-horizon"))
        self._clear_model()

        if len(assumption) > 0:
            const = And([c for c in assumption])
        else:
            const = BoolVal("True")

        if "model" in information.keys():
            model: Union[STLmcModel, None] = information["model"]
        else:
            model = None

        t_c = And([cache_const, const])
        declarations = make_declarations(t_c, model)
        time_declarations = declare_time_variables(max_bound, time_horizon)
        ode_definitions = define_ode(model)

        main_const = "\n".join(["(assert", translate(t_c, 2), ")"])

        cur_bound = get_cur_bound(t_c)
        time_const = make_time_const(cur_bound)

        dreal_const = "\n".join(["(set-logic QF_NRA_ODE)",
                                 declarations, time_declarations, ode_definitions,
                                 main_const, time_const, "(check-sat)", "(exit)"])

        rename_dict = make_flow_rename_dict(model)
        dreal_const = rename_flow(dreal_const, rename_dict)

        return self._check_sat(dreal_const)

    def _check_sat(self, dreal_const: str):
        dreal_section = self._config.get_section("dreal")
        common_section = self._config.get_section("common")
        ode_step = dreal_section.get_value("ode-step")
        ode_order = dreal_section.get_value("ode-order")
        exec_path = dreal_section.get_value("executable-path")

        str_file_name = "dreal_model" + str(random.random())
        with open(str_file_name + ".smt2", 'w') as mf:
            mf.write(dreal_const)

        current_os = check_os()
        if "macOS" in current_os:
            dreal_exec = "{}/dReal-darwin".format(exec_path)
        elif "Linux" in current_os:
            dreal_exec = "{}/dReal".format(exec_path)
        else:
            raise NotSupportedError("dreal is not supported for current os")

        model_file_name = "{}.smt2".format(str_file_name)
        # print(model_file_name)
        proc = subprocess.Popen(
            [dreal_exec, model_file_name, "--short_sat", "--model"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)

        start_time = time.time()
        stdout, stderr = proc.communicate()
        end_time = time.time()

        # self.set_time("solving timer", end_time - start_time)
        stdout_str = stdout.decode()
        stderr_str = stderr.decode()
        output_str = "{}\n{}".format(stdout.decode(), stderr.decode())
        # print(f'[exited with {proc.returncode}]')
        # if stdout:
        #     print(f'[stdout]\n{stdout.decode()}')
        # if stderr:
        #     print(f'[stderr]\n{stderr.decode()}')

        # if os.path.isfile(model_file_name):
        #     os.remove(model_file_name)

        # if "currentMode" in output_str:

        if "delta-sat" in output_str and "Solution" in output_str:
            cont_var_list = stdout_str[len("Solution:\n"): -1].split("\n")
            bool_var_list = stderr_str.split("\n")

            result_model = list()
            result_model.extend(cont_var_list)
            result_model.extend(bool_var_list)
            result_model.remove("")

            self._model = result_model

            return SMTSolver.sat
        elif "unsat" in stdout.decode():
            return SMTSolver.unsat
        else:
            return SMTSolver.unknown

    def make_assignment(self):
        if self._model is None:
            raise Exception("Dreal solver error occurred during making assignment (no model exists)")
        return DrealAssignment(self._model)

    def push(self):
        self._cache.append(list())

    def pop(self):
        self._cache.pop(len(self._cache) - 1)

    def reset(self):
        self._cache.clear()
        self._clear_model()

    def add(self, formula: Formula):
        self._cache[len(self._cache) - 1].append(formula)

    def assert_and_track(self, formula: Formula, track_id: str):
        pass

    def unsat_core(self):
        pass

    def _get_cache_const(self):
        consts = list()
        for c_list in self._cache:
            consts.extend(c_list)

        if len(consts) > 0:
            return And(consts)
        else:
            return BoolVal("True")

    def _clear_model(self):
        self._model = None


class DrealAssignment(Assignment):
    def __init__(self, dreal_model):
        self._dreal_model = dreal_model
        Assignment.__init__(self)

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
    def _get_assignments(self):
        new_dict = dict()
        duration_dict = dict()
        for e in self._dreal_model:
            # filter any messages not related to assignment
            if ":" in e and "=" in e:
                [var_decl, value] = e.split("=")
                [var_name, var_type] = var_decl.split(":")
                var_name = var_name.replace(" ", "")
                if "Bool" in var_type:
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

    def eval(self, const: Formula):
        pass


def make_declarations(formula: Formula, model: Union[STLmcModel, None]):
    declarations = set()

    vs = get_vars(formula)
    if model is None:
        for v in vs:
            dv = dreal_available_var(v)
            declarations.add(declare_variable(dv))
    else:
        for v in vs:
            nv = non_indexed_var(v)
            dv = dreal_available_var(v)
            if nv in model.range_info:
                declarations.add(declare_cont_variable(dv, model.range_info[nv]))
            else:
                if not is_tau(dv):
                    declarations.add(declare_variable(dv))

    return "\n".join(declarations)


def declare_time_variables(max_bound: int, time_horizon: float):
    declarations = set()
    for b in range(max_bound + 1):
        declarations.add("(declare-fun tau_{} () Real [0, {}])".format(b, time_horizon))
        declarations.add("(declare-fun tau_{} () Real [0, {}])".format(b + 1, time_horizon))

    for b in range(max_bound + 1):
        declarations.add("(declare-fun time_{} () Real [0, {}])".format(b, time_horizon))
    return "\n".join(declarations)


def make_time_const(cur_bound: int):
    consts = set()
    for b in range(cur_bound + 1):
        consts.add("(assert (= time_{} (- tau_{} tau_{})))".format(b, b + 1, b))
    return "\n".join(consts)


def get_cur_bound(formula: Formula):
    vs = get_vars(formula)
    cur_bound = -1

    for v in vs:
        if "@" in v.id:
            bound = get_bound_from_var(v)
            if bound > cur_bound:
                cur_bound = bound

    if cur_bound < 0:
        raise NotSupportedError("cannot determine current bound")

    return cur_bound


def define_ode(model: Union[STLmcModel, None]):
    if model is None:
        return ""
    else:
        ode_definitions = set()
        abs_dict = model.get_abstraction()

        for _, k in abs_dict.items():
            if isinstance(k, Integral):
                ode_definitions.add(define_flow(k.dynamics, str(hash(k.dynamics))))
        return "\n".join(ode_definitions)


def rename_flow(dreal_const: str, rename_dict: Dict):
    for flow_name in rename_dict:
        dreal_const = dreal_const.replace(flow_name, rename_dict[flow_name])
    return dreal_const


def make_flow_rename_dict(model: Union[STLmcModel, None]):
    if model is None:
        return dict()
    else:
        rename_dict = dict()
        abs_dict = model.get_abstraction()
        for index, (_, k) in enumerate(abs_dict.items()):
            if isinstance(k, Integral):
                rename_dict["flow_{}".format(hash(k.dynamics))] = "flow_{}".format(index)
        return rename_dict


def declare_variable(v: Variable):
    return "(declare-fun {} () {})".format(v.id, v.type.capitalize())


def declare_cont_variable(v: Variable, domain: Interval):
    return "(declare-fun {} () {} {})".format(v.id, v.type.capitalize(), domain)


def define_flow(dyn: Dynamics, name: str):
    flow = list()
    for v, e in zip(dyn.vars, dyn.exps):
        flow.append("  (= d/dt[{}] {})".format(v, translate(e)))
    return "(define-ode flow_{} (\n{}\n))".format(name, "\n".join(flow))


def check_os():
    return platform.platform()


@singledispatch
def translate(const: Formula, indent=0):
    raise NotSupportedError("fail to translate \"{}\" to Dreal object ".format(const))


@translate.register(Constant)
def _(const: Constant, indent=0):
    return indented_str(str(const.value).lower(), indent)


@translate.register(Variable)
def _(const: Variable, indent=0):
    v = dreal_available_var(const)
    return indented_str(v.id, indent)


@translate.register(Geq)
def _(const, indent=0):
    t = [
        indented_str("(>=", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Gt)
def _(const, indent=0):
    t = [
        indented_str("(>", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Leq)
def _(const, indent=0):
    t = [
        indented_str("(<=", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Lt)
def _(const, indent=0):
    t = [
        indented_str("(<", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Eq)
def _(const, indent=0):
    t = [
        indented_str("(=", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Neq)
def _(const, indent=0):
    return translate(Not(const.left == const.right), indent)


@translate.register(EqFormula)
def _(const, indent=0):
    t = [
        indented_str("(=", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(NeqFormula)
def _(const, indent=0):
    return translate(Not(const.left == const.right), indent)


@translate.register(Add)
def _(const, indent=0):
    t = [
        indented_str("(+", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Sub)
def _(const, indent=0):
    t = [
        indented_str("(-", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Pow)
def _(const, indent=0):
    t = [
        indented_str("(^", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Mul)
def _(const, indent=0):
    t = [
        indented_str("(*", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Div)
def _(const, indent=0):
    t = [
        indented_str("(/", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Neg)
def _(const, indent=0):
    t = [
        indented_str("(-", indent),
        indented_str("0", indent + 2),
        translate(const.child, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Sqrt)
def _(const, indent=0):
    t = [
        indented_str("(sqrt", indent),
        translate(const.child, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Sin)
def _(const, indent=0):
    t = [
        indented_str("(sin", indent),
        translate(const.child, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Cos)
def _(const, indent=0):
    t = [
        indented_str("(cos", indent),
        translate(const.child, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Tan)
def _(const, indent=0):
    x = translate(const.child, indent + 4)
    t = [
        indented_str("(/", indent),
        indented_str("(sin", indent + 2),
        x,
        indented_str(")", indent + 2),
        indented_str("(cos", indent + 2),
        x,
        indented_str(")", indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Arcsin)
def _(const, indent=0):
    t = [
        indented_str("(arcsin", indent),
        translate(const.child, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Arccos)
def _(const, indent=0):
    t = [
        indented_str("(arccos", indent),
        translate(const.child, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Arctan)
def _(const, indent=0):
    x = translate(const.child, indent + 4)
    t = [
        indented_str("(/", indent),
        indented_str("(cos", indent + 2),
        x,
        indented_str(")", indent + 2),
        indented_str("(sin", indent + 2),
        x,
        indented_str(")", indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(And)
def _(const, indent=0):
    if len(const.children) < 1:
        return indented_str("true", indent)
    elif len(const.children) == 1:
        return translate(const.children[0], indent)
    else:
        consts = [indented_str("(and", indent)]
        consts.extend([translate(c, indent + 2) for c in const.children])
        consts.append(indented_str(")", indent))
        return "\n".join(consts)


@translate.register(Or)
def _(const, indent=0):
    if len(const.children) < 1:
        return indented_str("true", indent)
    elif len(const.children) == 1:
        return translate(const.children[0], indent)
    else:
        consts = [indented_str("(or", indent)]
        consts.extend([translate(c, indent + 2) for c in const.children])
        consts.append(indented_str(")", indent))
        return "\n".join(consts)


@translate.register(Implies)
def _(const, indent=0):
    t = [
        indented_str("(=>", indent),
        translate(const.left, indent + 2),
        translate(const.right, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Not)
def _(const, indent=0):
    t = [
        indented_str("(not", indent),
        translate(const.child, indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(t)


@translate.register(Integral)
def _(const: Integral, indent=0):
    e_v = " ".join([str(v) for v in const.end_vector])
    s_v = " ".join([str(v) for v in const.start_vector])

    e_b = get_bound_from_vector(const.end_vector)
    s_b = get_bound_from_vector(const.start_vector)

    if e_b != s_b:
        raise NotSupportedError("bound of the integral must be the same")

    str_l = [
        indented_str("(=", indent),
        indented_str("[{}]".format(e_v), indent + 2),
        indented_str("(integral 0. time_{} [{}] flow_{})".format(e_b, s_v, hash(const.dynamics)), indent + 2),
        indented_str(")", indent)
    ]
    return "\n".join(str_l)


@translate.register(Forall)
def _(const: Forall, indent=0):
    cur_bound = get_bound_from_tau(const.start_tau)
    vs = get_vars(const.const)

    # build substitution
    subst = Substitution()
    for v in vs:
        subst.add(v, indexed_var_t(v, cur_bound))

    forall_c = subst.substitute(const.const)

    t = [
        indented_str("(forall_t {} [0 time_{}]".format(cur_bound + 1, cur_bound), indent),
        translate(forall_c, indent + 2),
        indented_str(")", indent)
    ]

    return "\n".join(t)


def get_bound_from_vector(v_l: List[Variable]):
    bound_list = [get_bound_from_var(v) for v in v_l]
    bound_set = set(bound_list)
    if len(bound_set) == 1:
        return bound_list[0]
    else:
        raise NotSupportedError("invalid bound information found")


def get_bound_from_var(v: Variable):
    return int(v.id.split("@")[1])


def get_bound_from_tau(v: Variable):
    return int(v.id.split("_")[1])


def dreal_available_var(v: Variable):
    v_id = v.id.replace("{", "@").replace("}", "@").replace(",", "@")
    return variable(v_id, v.type)


def is_tau(v: Variable):
    return "tau_" in v.id and isinstance(v, Real)
