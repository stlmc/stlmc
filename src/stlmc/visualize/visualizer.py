import abc
import errno
import itertools
import os
from typing import List, Dict, Set, Tuple

import numpy
import numpy as np
import sympy
from bokeh.embed import components
from bokeh.io import output_file, save
from bokeh.models import HoverTool, CrosshairTool, Legend, DataRange1d
from bokeh.palettes import Dark2_5 as palette
from bokeh.plotting import column
from scipy.integrate import odeint

from ..constraints.constraints import *
from ..constraints.operations import *
from ..exception.exception import *
from bokeh.plotting import figure, show


class Projector:
    def __init__(self, assignment, mode_var_dict: Dict[str, Variable],
                 proposition_dict: Dict[Variable, Constraint], modules: Dict):
        self.assignment = assignment
        self.mode_var_dict = mode_var_dict
        self.proposition_dict = proposition_dict
        self.modules = modules

    def find_all_with_keywords(self, keyword: str) -> List[Variable]:
        result = list()
        for v in self.assignment:
            if keyword in v.id:
                result.append(v)
        return result

    # return sorted list of variables
    def get_variable_points(self) -> List[Variable]:
        tau_list = self.find_all_with_keywords("tau")
        return sorted(tau_list, key=lambda v: int(v.id[4:]))

    def get_mode_vars(self) -> Set[Variable]:
        return set(self.proposition_dict.keys()).union(self.mode_var_dict.values())

    def get_ordered_mode_vars(self):
        mode_vars = self.find_all_with_keywords("currentMode_")
        ordered_mode_vars = sorted(mode_vars, key=lambda v: int(v.id[len("currentMode_"):]))
        return ordered_mode_vars

    def get_max_bound(self):
        ordered_mode_vars = self.get_ordered_mode_vars()
        last = ordered_mode_vars[len(ordered_mode_vars) - 1]
        last_id = int(last.id[len("currentMode_"):])
        return last_id

    # get module ordering
    def get_ordered_modules(self) -> List[Dict]:
        # find module ids
        ordered_mode_vars = self.get_ordered_mode_vars()
        ordered_module_ids = list()
        for v in ordered_mode_vars:
            ordered_module_ids.append(int(float(self.assignment[v].value)))
        #
        result = list()
        for module_id in ordered_module_ids:
            result.append(self.modules[module_id])

        return result


def sample_max(time_list: List[List[float]]):
    t_max = -1
    for time_points in time_list:
        for time_point in time_points:
            if t_max < time_point:
                t_max = time_point
    return t_max


class TimeSampler:
    def __init__(self, projector: Projector):
        self.projector = projector

    def generate_samples(self, endpoint=True) -> List[List[float]]:
        np_ndarry_list: List[numpy.ndarray] = list()
        variable_points = self.projector.get_variable_points()
        assignment = self.projector.assignment
        # print(self.taus)
        for i, _ in enumerate(variable_points):
            if i < len(variable_points) - 1:
                tau = assignment[variable_points[i]]
                next_tau = assignment[variable_points[i + 1]]

                # use sympy for parsing fraction into decimal
                # if i == 0:
                #     next_tau_value_sympy = sympy.parse_expr(tau.value)
                #     # convert sympy object into python object
                #     cur_tau_value = 0.0
                #     next_tau_value = float(next_tau_value_sympy.evalf())
                #     np_ndarry_list.append(np.linspace(cur_tau_value, next_tau_value))

                cur_tau_value_sympy = sympy.parse_expr(tau.value)
                next_tau_value_sympy = sympy.parse_expr(next_tau.value)

                # convert sympy object into python object
                cur_tau_value = float(cur_tau_value_sympy.evalf())
                next_tau_value = float(next_tau_value_sympy.evalf())
                np_ndarry_list.append(np.linspace(cur_tau_value, next_tau_value, endpoint=endpoint))

        time_list: List[List[float]] = list()

        for np_ndarry in np_ndarry_list:
            time_points: List[float] = list()
            for ii in np_ndarry:
                time_points.append(ii.item())
            time_list.append(time_points)

        return time_list


class DiscreteSampler:
    def __init__(self, projector: Projector):
        self.projector = projector

    # generate samples at bound ...
    def generate_samples_at(self, time_samples: List[float], bound):
        mode_variables = self.projector.get_mode_vars()
        assignment = self.projector.assignment
        type_dict = {'real': Real, 'bool': Bool, 'int': Int}
        result: Dict[Variable, List[float]] = dict()
        for v in mode_variables:
            var_id = "{}_{}".format(v.id, bound)
            var_type = v.type
            v_obj = type_dict[var_type](var_id)
            if v_obj in assignment:
                v_val = assignment[v_obj]

                if var_type == 'bool':
                    var_value = 1 if v_val.value == "True" else -1
                else:
                    var_value_sympy = sympy.parse_expr(v_val.value)
                    var_value = float(var_value_sympy)

                result[v] = list()
                for _ in time_samples:
                    result[v].append(var_value)

        return result


class PointSampler:
    @abc.abstractmethod
    def generate_samples(self, time_samples: List[float], dynamic: Dynamics, initial_values: List[float]):
        # for a given dynamics, and time samples, this generates sample points.
        pass


class SolutionPointSampler(PointSampler):
    def generate_samples(self, time_samples: List[float], dynamic: Dynamics, initial_values: List[float]):
        sample_dict: Dict[Variable, List[float]] = dict()

        # normalize
        base = time_samples[0]
        time_samples = [time - base for time in time_samples]

        assignment = dict()
        time = sympy.parse_expr("time")
        for index, v in enumerate(dynamic.vars):
            assignment[sympy.parse_expr(str(v.id))] = sympy.parse_expr(str(initial_values[index]))

        for index, v in enumerate(dynamic.vars):
            v_samples = list()
            for time_sample in time_samples:
                assignment[time] = sympy.parse_expr(str(time_sample))
                dyn = sympy.parse_expr(infix(dynamic.exps[index]))
                v_samples.append(float(dyn.evalf(10, assignment)))
            sample_dict[v] = v_samples
        return sample_dict


class OdePointSampler(PointSampler):
    def generate_samples(self, time_samples: List[float], dynamic: Dynamics, initial_values: List[float]):
        res = odeint(lambda z, t: [infix_float(dyn, z, dynamic.vars) for dyn in dynamic.exps], initial_values,
                     time_samples)
        sample_dict: Dict[Variable, List[float]] = dict()

        for v in dynamic.vars:
            v_samples = list()
            for sample in res:
                v_index = dynamic.vars.index(v)
                v_samples.append(sample[v_index])
            sample_dict[v] = v_samples
        return sample_dict


class Visualizer:
    def __init__(self):
        self.assignment = dict()
        self.visualize_dict = dict()
        self.plot = None

    def write(self, file_name):
        if self.plot is None:
            raise NotSupportedError("plot must not be none!")
        output_file(filename="{}.html".format(file_name))
        save(self.plot)
        self.plot = None
        print("write counterexample graphs: \'{}.html\'".format(file_name))

    def generate_data(self, assignment: dict, modules: dict, mode_var_dict: Dict[str, Variable],
                      propositions: Dict[Variable, Constraint], cont_var_dict: dict, prop_dict: dict,
                      formula: Constraint, formula_label: str, delta: float):
        self.assignment.clear()
        ff = substitution(formula, prop_dict)
        subformulas, formula_id_dict = sub_formula(ff)

        projector = Projector(assignment, mode_var_dict, propositions, modules)

        max_bound = projector.get_max_bound()
        time_sampler = TimeSampler(projector)
        time_samples_list = time_sampler.generate_samples()
        time_max = sample_max(time_samples_list)

        ordered_modules = projector.get_ordered_modules()
        c_val = self.make_cont_values(assignment, cont_var_dict, max_bound)

        point_samples: Dict[Variable, List[List[float]]] = dict()
        discrete_samples: Dict[Variable, List[List[float]]] = dict()

        op = OdePointSampler()
        sp = SolutionPointSampler()
        ds = DiscreteSampler(projector)

        for interval_index, module in enumerate(ordered_modules):
            initial_values = list()
            for v in module["flow"].vars:
                initial_values.append(c_val[v.id][interval_index][0])

            dynamics = module["flow"]
            if isinstance(dynamics, Ode):
                gen_dict = op.generate_samples(time_samples_list[interval_index], dynamics, initial_values)

            else:
                gen_dict = sp.generate_samples(time_samples_list[interval_index], dynamics, initial_values)

            for v in gen_dict:
                if v in point_samples:
                    point_samples[v].append(gen_dict[v])
                else:
                    point_samples[v] = [gen_dict[v].copy()]

            discrete_dict = ds.generate_samples_at(time_samples_list[interval_index], interval_index)
            for v in discrete_dict:
                if v in discrete_samples:
                    discrete_samples[v].append(discrete_dict[v])
                else:
                    discrete_samples[v] = [discrete_dict[v]]

        robustness_dict = dict()
        print("calculate robustness values ...")
        dp_table: Dict[Tuple[Formula, float], float] = dict()
        for f in subformulas:
            robustness_dict[f] = list()
            for time_sample in time_samples_list:
                sample_list = list()
                for time in time_sample:
                    rob = robustness(f, point_samples, discrete_samples, time, time_samples_list, time_max, dp_table)
                    sample_list.append(rob)
                robustness_dict[f].append(sample_list)

        return point_samples, robustness_dict, time_samples_list, formula_id_dict, formula_label, delta

    def generate_plot(self, assignment: dict, modules: dict, mode_var_dict: Dict[str, Variable],
                      propositions: Dict[Variable, Constraint], cont_var_dict: dict, prop_dict: dict,
                      formula: Constraint, formula_label: str, delta: float, user_defined_groups: Dict[int, Set[str]]):

        point_samples, robustness_dict, time_samples_list, formula_id_dict, _, _ = self.generate_data(assignment,
                                                                                                      modules,
                                                                                                      mode_var_dict,
                                                                                                      propositions,
                                                                                                      cont_var_dict,
                                                                                                      prop_dict,
                                                                                                      formula,
                                                                                                      formula_label,
                                                                                                      delta)
        user_defined_groups_list = list(user_defined_groups.values())
        robust_variables = set()
        formula_dict: Dict[str, Formula] = dict()
        for f in robustness_dict:
            robust_variables.add("{}_{}".format(formula_label, formula_id_dict[f]))
            formula_dict[formula_id_dict[f]] = f

        v_names: List[Variable] = list(sorted(point_samples.keys(), key=lambda _v: _v.id))
        v_name_dict: Dict[str, Variable] = dict()

        for v in point_samples:
            v_name_dict[v.id] = v

        v_names_index: Dict[str, int] = dict()
        for index, v_name in enumerate(v_names):
            v_names_index[v_name.id] = index

        v_names_set = set(map(lambda x: x.id, v_names))
        if len(user_defined_groups) > 0:
            # disjoint checking
            pairwise_disjoint_check(user_defined_groups_list)
            state_vars, robust_vars = split_groups(user_defined_groups_list, v_names_set, robust_variables)
            state_vars.append(v_names_set.difference(flatten(state_vars)))
            robust_vars.append(robust_variables.difference(flatten(robust_vars)))
        else:
            state_vars = [v_names_set.copy()]
            robust_vars = [robust_variables.copy()]

        TOOLTIPS = [
            ("(x,y)", "($x, $data_y)"),
        ]

        main_list = list()
        main_representative = None
        for g_index, group in enumerate(state_vars):
            if len(group) < 1:
                continue
            crosshair_tool = CrosshairTool(line_alpha=0.8)
            colors = itertools.cycle(palette)

            if main_representative is None:
                main_figure = figure(title="continuous state variables", x_axis_label='time', y_axis_label='values',
                                     sizing_mode="scale_width", height=210, toolbar_location="above",
                                     x_range=DataRange1d(start=0.0, bounds='auto'))
            else:
                main_figure = figure(title="continuous state variables", x_axis_label='time', y_axis_label='values',
                                     sizing_mode="scale_width", height=210, toolbar_location="above",
                                     x_range=main_representative.x_range)

            main_figure.add_tools(crosshair_tool)
            main_figure.min_border_top = 75
            main_figure.min_border_bottom = 75

            legend_main_figure = list()
            for v_name in group:
                v = v_name_dict[v_name]
                multi_line = main_figure.multi_line(time_samples_list, point_samples[v],
                                                    line_width=2, color=next(colors))
                main_figure.add_tools(HoverTool(renderers=[multi_line], tooltips=TOOLTIPS, mode="mouse",
                                                line_policy="interp", toggleable=False))
                legend_main_figure.append(("{}".format(v), [multi_line]))

            legend = Legend(items=legend_main_figure, location="center")
            legend.click_policy = "hide"
            main_figure.add_layout(legend, 'right')
            main_list.append(main_figure)

            if g_index == 0:
                main_representative = main_figure

        if main_representative is None:
            raise ValueError("there are no state variables")

        rob_list = list()
        for g_index, group in enumerate(robust_vars):
            if len(group) < 1:
                continue
            rob_figure = figure(title="robustness", x_axis_label='time', y_axis_label='values', tooltips=TOOLTIPS,
                                sizing_mode="scale_width", height=150, toolbar_location="above",
                                x_range=main_representative.x_range)

            rob_figure.ray([0], [0], angle_units='deg', length=0, angle=0, line_color="black")
            robust_degree = rob_figure.ray([0], [delta], angle_units='deg', length=0, angle=0, line_color="red",
                                           line_width=1.5, line_dash="dashed")

            legend_rob_lines = [("\u03B5", [robust_degree])]
            # assert all formulas have valid ids

            sorted_ids = list(sorted(formula_id_dict.keys(), key=lambda _f: formula_id_dict[_f]))

            for f in sorted_ids:
                if f in robustness_dict:
                    formula_id = formula_id_dict[f]
                    if "{}_{}".format(formula_label, formula_id) not in group:
                        continue
                    # print("{}_{} ---> {}".format(formula_label, formula_id_dict[f], f))
                    rob_line = rob_figure.multi_line(time_samples_list, robustness_dict[f],
                                                     line_width=2, color=next(colors))
                    formula_name = "{}".format(formula_label) if formula_id == 0 else "{}_{}".format(formula_label,
                                                                                                     formula_id)
                    legend_rob_lines.append((formula_name, [rob_line]))

            rob_legend = Legend(items=legend_rob_lines, location="center")
            rob_legend.click_policy = "hide"
            rob_figure.add_layout(rob_legend, 'right')
            rob_list.append(rob_figure)

        print("generating counterexample visualization")
        self.plot = column(children=[*main_list, *rob_list], sizing_mode="scale_both")


    @staticmethod
    def make_cont_values(assignment: dict, cont_var_dict: dict, max_bound):
        result = dict()
        for var in cont_var_dict:
            sub_result = list()
            for i in range(max_bound + 1):
                initial_var_id = var.id + "_" + str(i) + "_0"
                final_var_id = var.id + "_" + str(i) + "_t"

                initial_value_sympy = sympy.parse_expr(assignment[Real(initial_var_id)].value)
                final_value_sympy = sympy.parse_expr(assignment[Real(final_var_id)].value)

                initial_value = float(initial_value_sympy.evalf())
                final_value = float(final_value_sympy.evalf())

                sub_result.append((initial_value, final_value))

            result[var.id] = sub_result

        return result


@singledispatch
def infix_float(const: Constraint, vec, var_list: list):
    raise NotSupportedError("cannot convert this: {}".format(const))


@infix_float.register(Neg)
def _(const: Neg, vec, var_list: list):
    return - infix_float(const.child, vec, var_list)


@infix_float.register(IntVal)
def _(const: IntVal, vec, var_list: list):
    return int(const.value)


@infix_float.register(RealVal)
def _(const: RealVal, vec, var_list: list):
    return float(const.value)


@infix_float.register(Int)
def _(const: Int, vec, var_list: list):
    return vec[var_list.index(const)]


@infix_float.register(Real)
def _(const: Real, vec, var_list: list):
    return vec[var_list.index(const)]


@infix_float.register(Add)
def _(const: Add, vec, var_list: list):
    return infix_float(const.left, vec, var_list) + infix_float(const.right, vec, var_list)


@infix_float.register(Sub)
def _(const: Sub, vec, var_list: list):
    return infix_float(const.left, vec, var_list) - infix_float(const.right, vec, var_list)


@infix_float.register(Mul)
def _(const: Mul, vec, var_list: list):
    return infix_float(const.left, vec, var_list) * infix_float(const.right, vec, var_list)


@infix_float.register(Div)
def _(const: Div, vec, var_list: list):
    return infix_float(const.left, vec, var_list) / infix_float(const.right, vec, var_list)


@infix_float.register(Pow)
def _(const: Pow, vec, var_list: list):
    return infix_float(const.left, vec, var_list) ** infix_float(const.right, vec, var_list)


def get_sub_time_samples(time_sample_list: List[List[float]], start: float, end: float, time_max: float) -> List[float]:
    # ignore time points beyond time bound
    if start > time_max:
        start = time_max

    if end > time_max:
        end = time_max

    times: List[float] = list()
    for time_samples in time_sample_list:
        times.extend(time_samples)

    s_index = -1
    # find the first matching time point
    for index, t in enumerate(times):
        if t >= start:
            s_index = index
            break

    e_index = -1
    rev_times = reversed(times)
    for index, t in enumerate(rev_times):
        if t <= end:
            e_index = len(times) - index - 1
            break

    if s_index == -1 or e_index == -1:
        # print(time_sample_list)
        # print("from {} to {}".format(start, end))
        raise NotSupportedError("cannot find sub time samples")

    sub_time_samples: List[float] = list()

    for index, t in enumerate(times):
        if s_index <= index <= e_index:
            sub_time_samples.append(t)

    return sub_time_samples


@singledispatch
def robustness(const: Constraint, point_samples: Dict[Variable, List[List[float]]],
               discrete_samples: Dict[Variable, List[List[float]]],
               time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Bool)
def _(const: Implies, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Bool, RealVal] = dict()
                for v in discrete_samples:
                    v_val_str = str(discrete_samples[v][interval_index][index])
                    # this is not right implementation
                    if v_val_str == "1":
                        substitute_dict[v] = RealVal("oo")
                    if v_val_str == "-1":
                        substitute_dict[v] = RealVal("-oo")
                    if v_val_str == "0":
                        substitute_dict[v] = RealVal("0")
                expr = substitution(const, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, t)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Implies)
def _(const: Implies, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    robust_value = robustness(Or([Not(const.left), const.right]), point_samples, discrete_samples, time, times,
                              time_max, dp_table)
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(BoolVal)
def _(const: BoolVal, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    if const.value == "True":
        robust_value = float("inf")
        dp_table[(const, time)] = robust_value
        return robust_value
    if const.value == "False":
        robust_value = float("-inf")
        dp_table[(const, time)] = robust_value
        return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Eq)
def _(const: Eq, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    return robustness(And([Leq(const.left, const.right),Geq(const.left, const.right)]), 
                      point_samples, discrete_samples, time, times, time_max, dp_table)


@robustness.register(Geq)
def _(const: Geq, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    lhs = const.left - const.right
    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Real, RealVal] = dict()
                for v in point_samples:
                    substitute_dict[v] = RealVal(str(point_samples[v][interval_index][index]))
                expr = substitution(lhs, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, time)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Gt)
def _(const: Gt, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    lhs = const.left - const.right
    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Real, RealVal] = dict()
                for v in point_samples:
                    substitute_dict[v] = RealVal(str(point_samples[v][interval_index][index]))
                expr = substitution(lhs, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, time)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Leq)
def _(const: Leq, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    lhs = const.right - const.left
    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Real, RealVal] = dict()
                for v in point_samples:
                    substitute_dict[v] = RealVal(str(point_samples[v][interval_index][index]))
                expr = substitution(lhs, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, time)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Lt)
def _(const: Leq, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    lhs = const.right - const.left
    for interval_index, time_samples in enumerate(times):
        for index, t in enumerate(time_samples):
            if t == time:
                substitute_dict: Dict[Real, RealVal] = dict()
                for v in point_samples:
                    substitute_dict[v] = RealVal(str(point_samples[v][interval_index][index]))
                expr = substitution(lhs, substitute_dict)
                robust_value = float(str(sympy.parse_expr("{}".format(infix(expr)))))
                dp_table[(const, time)] = robust_value
                return robust_value
    raise NotSupportedError("cannot calculate robustness of a \"{}\"".format(const))


@robustness.register(Not)
def _(const: Not, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    robust_value = - robustness(const.child, point_samples, discrete_samples, time, times, time_max, dp_table)
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(And)
def _(const: And, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    robust_value = min(
        [robustness(c, point_samples, discrete_samples, time, times, time_max, dp_table) for c in const.children])
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(Or)
def _(const: Or, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    robust_value = max(
        [robustness(c, point_samples, discrete_samples, time, times, time_max, dp_table) for c in const.children])
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(UntilFormula)
def _(const: UntilFormula, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    intv_left = float(str(sympy.parse_expr(const.local_time.left.value, evaluate=True)))
    intv_right = float(str(sympy.parse_expr(const.local_time.right.value, evaluate=True)))

    t_primes = get_sub_time_samples(times, time + intv_left, time + intv_right, time_max)

    robust_value = max([min(robustness(const.left, point_samples, discrete_samples, t_prime, times, time_max, dp_table),
                            min(
                                [robustness(const.right, point_samples, discrete_samples, t_prime_prime, times,
                                            time_max, dp_table)
                                 for t_prime_prime in get_sub_time_samples(times, time, t_prime, time_max)])
                            ) for t_prime in t_primes])

    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(ReleaseFormula)
def _(const: ReleaseFormula, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]
    intv_left = float(str(sympy.parse_expr(const.local_time.left.value, evaluate=True)))
    intv_right = float(str(sympy.parse_expr(const.local_time.right.value, evaluate=True)))

    t_primes = get_sub_time_samples(times, time + intv_left, time + intv_right, time_max)
    robust_value = min(
        [max(robustness(const.left, point_samples, discrete_samples, t_prime, times, time_max, dp_table),
             max(
                 [robustness(const.right, point_samples, discrete_samples, t_prime_prime, times, time_max, dp_table)
                  for t_prime_prime in get_sub_time_samples(times, time, t_prime, time_max)])
             ) for t_prime in t_primes])
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(GloballyFormula)
def _(const: GloballyFormula, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    intv_left = float(str(sympy.parse_expr(const.local_time.left.value, evaluate=True)))
    intv_right = float(str(sympy.parse_expr(const.local_time.right.value, evaluate=True)))

    t_primes = get_sub_time_samples(times, time + intv_left, time + intv_right, time_max)
    robust_value = min(
        [robustness(const.child, point_samples, discrete_samples, t_prime, times, time_max, dp_table) for t_prime in
         t_primes])
    dp_table[(const, time)] = robust_value
    return robust_value


@robustness.register(FinallyFormula)
def _(const: FinallyFormula, point_samples: Dict[Variable, List[List[float]]],
      discrete_samples: Dict[Variable, List[List[float]]],
      time: float, times: List[List[float]], time_max: float, dp_table: Dict[Tuple[Formula, float], float]):
    if (const, time) in dp_table:
        return dp_table[(const, time)]

    intv_left = float(str(sympy.parse_expr(const.local_time.left.value, evaluate=True)))
    intv_right = float(str(sympy.parse_expr(const.local_time.right.value, evaluate=True)))

    t_primes = get_sub_time_samples(times, time + intv_left, time + intv_right, time_max)
    robust_value = max(
        [robustness(const.child, point_samples, discrete_samples, t_prime, times, time_max, dp_table) for t_prime in
         t_primes])
    dp_table[(const, time)] = robust_value
    return robust_value


def interval_string(interval: Interval):
    interval_left_ends = {True: "[", False: "("}
    interval_right_ends = {True: "]", False: ")"}

    interval_tmp = list()

    interval_tmp.append(interval_left_ends[interval.left_end])
    interval_tmp.append("{},{}".format(interval.left, interval.right))
    interval_tmp.append(interval_right_ends[interval.right_end])
    return "".join(interval_tmp)


def sub_formula(formula: Formula) -> Tuple[Set, Dict]:
    def _id_gen():
        _id = -1
        while True:
            _id += 1
            yield _id

    assert isinstance(formula, Formula)

    gen_id = _id_gen()
    formula_id_dict = dict()
    set_of_formulas = set()

    # first children
    root = (next(gen_id), formula)

    waiting_queue = set()
    waiting_queue.add(root)
    set_of_formulas.add(formula)

    while len(waiting_queue) > 0:
        f_id, f = waiting_queue.pop()
        if f in formula_id_dict:
            continue
        formula_id_dict[f] = f_id

        if is_proposition(f):
            set_of_formulas.add(f)
        elif isinstance(f, UnaryFormula):
            set_of_formulas.add(f)
            waiting_queue.add((next(gen_id), f.child))
        elif isinstance(f, BinaryFormula):
            set_of_formulas.add(f)
            if isinstance(f, Implies):
                waiting_queue.add((next(gen_id), Not(f.left)))
            else:
                waiting_queue.add((next(gen_id), f.left))
            waiting_queue.add((next(gen_id), f.right))
        elif isinstance(f, MultinaryFormula):
            set_of_formulas.add(f)
            for child in f.children:
                waiting_queue.add((next(gen_id), child))
        else:
            del formula_id_dict[f]
            continue
    return set_of_formulas, formula_id_dict


@singledispatch
def formula2latex(formula: Formula):
    raise NotSupportedError("cannot translate formula to latex")


# assume binary
@formula2latex.register(And)
def _(formula: And):
    assert len(formula.children) == 2
    return "({} and {})".format(formula2latex(formula.children[0]), formula2latex(formula.children[1]))


@formula2latex.register(Or)
def _(formula: Or):
    assert len(formula.children) == 2
    return "({} or {})".format(formula2latex(formula.children[0]), formula2latex(formula.children[1]))


@formula2latex.register(Implies)
def _(formula: Implies):
    return "({} \\rightarrow {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Lt)
def _(formula: Lt):
    return "({} < {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Leq)
def _(formula: Leq):
    return "({} \\leq {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Gt)
def _(formula: Gt):
    return "({} > {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Geq)
def _(formula: Geq):
    return "({} \\geq {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Eq)
def _(formula: Eq):
    return "({} = {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Neq)
def _(formula: Neq):
    return "({} \\neq {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Not)
def _(formula: Not):
    return "(\\neg {})".format(formula2latex(formula.child))


@formula2latex.register(Add)
def _(formula: Add):
    return "({} + {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Sub)
def _(formula: Sub):
    return "({} - {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Mul)
def _(formula: Mul):
    return "({} * {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Div)
def _(formula: Add):
    return "({} / {})".format(formula2latex(formula.left), formula2latex(formula.right))


@formula2latex.register(Sqrt)
def _(formula: Sqrt):
    return "(\\sqrt{{{}}})".format(formula2latex(formula.child))


@formula2latex.register(Variable)
def _(formula: Variable):
    return "{}".format(formula.id)


@formula2latex.register(Constant)
def _(formula: Constant):
    return "{}".format(str(formula.value).lower())


@formula2latex.register(UntilFormula)
def _(formula: UntilFormula):
    return "{} \\mathbf{{U}}_{{{}}} {}".format(formula2latex(formula.left), interval_string(formula.local_time),
                                               formula2latex(formula.right))


@formula2latex.register(ReleaseFormula)
def _(formula: ReleaseFormula):
    return "{} \\mathbf{{R}}_{{{}}} {}".format(formula2latex(formula.left), interval_string(formula.local_time),
                                               formula2latex(formula.right))


@formula2latex.register(GloballyFormula)
def _(formula: GloballyFormula):
    return "\\square_{{{}}} {}".format(interval_string(formula.local_time),
                                       formula2latex(formula.child))


@formula2latex.register(FinallyFormula)
def _(formula: FinallyFormula):
    return "\\lozenge_{{{}}} {}".format(interval_string(formula.local_time),
                                        formula2latex(formula.child))


def split_groups(groups: List[Set[str]], state_vars: Set[str], robust_vars: Set[str]):
    state_groups = list()
    robust_groups = list()

    waiting_queue = groups.copy()
    while len(waiting_queue) > 0:
        group = waiting_queue.pop()

        # state variables
        if group.issubset(state_vars):
            state_groups.append(group)
        elif group.issubset(robust_vars):
            robust_groups.append(group)
        else:
            raise ValueError("group contains wrong variables : {}".format(group))
    return state_groups, robust_groups


def pairwise_disjoint_check(groups: List[Set[str]]):
    waiting_queue = groups.copy()
    while len(waiting_queue) > 0:
        group = waiting_queue.pop()
        for g in waiting_queue:
            intersection_vars = g.intersection(group)
            if len(intersection_vars) > 0:
                raise ValueError("state variables {} belong to multiple groups".format(intersection_vars))


def flatten(groups: List[Set[str]]) -> Set[str]:
    flat_set = set()
    for group in groups:
        flat_set.update(group)
    return flat_set
