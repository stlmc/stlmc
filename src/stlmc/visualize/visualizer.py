import errno
import itertools
import os
from typing import List, Dict, Set, Tuple

import sympy
from bokeh.embed import components
from bokeh.io import output_file, save
from bokeh.models import HoverTool, CrosshairTool, Legend, DataRange1d
from bokeh.palettes import Dark2_5 as palette
from bokeh.plotting import column

from ..constraints.constraints import *
from ..constraints.operations import *
from ..artifacts.formula_index import index_subformulas as sub_formula
from ..exceptions import *
from .latex import formula2latex, interval_string
from .grouping import flatten, pairwise_disjoint_check, split_groups
from .projection import Projector
from .robustness import robustness
from .sampling import (
    DiscreteSampler, OdePointSampler, PointSampler, SolutionPointSampler,
    TimeSampler, get_sub_time_samples, sample_max,
)
from bokeh.plotting import figure, show


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

    @staticmethod
    def _model_text(value):
        # Jump targets use an intentionally unusual suffix internally so they
        # cannot collide with current-state variables.  Restore the model
        # language's apostrophe notation in human-readable output.
        return str(value).replace("##$%^&$%^&##'", "'")

    @staticmethod
    def _assignment_value(assignment, variable):
        value = assignment.get(variable)
        return value.value if value is not None else "?"

    @staticmethod
    def _range_text(value_range):
        left_closed, left, right, right_closed = value_range
        left_bracket = "[" if left_closed else "("
        right_bracket = "]" if right_closed else ")"
        return "{}{}, {}{}".format(left_bracket, left, right, right_bracket)

    def write_text(self, file_name, assignment: dict, modules: dict,
                   mode_var_dict: Dict[str, Variable],
                   propositions: Dict[Variable, Constraint], cont_var_dict: dict,
                   prop_dict: dict, formula: Constraint, formula_label: str,
                   delta: float, init=None, const_dict=None):
        projector = Projector(assignment, mode_var_dict, propositions, modules)
        ordered_modules = projector.get_ordered_modules()
        max_bound = projector.get_max_bound()
        variable_points = projector.get_variable_points()
        cont_values = self.make_cont_values(assignment, cont_var_dict, max_bound)
        expanded_formula = substitution(formula, prop_dict)

        heading = "Witness" if file_name.endswith(".witness") else "Counterexample"
        lines = [
            heading,
            "=" * len(heading),
            "",
            "goal: {}".format(formula_label),
            "formula: {}".format(self._model_text(expanded_formula)),
            "bound: {}".format(max_bound),
            "delta: {}".format(delta),
        ]

        if const_dict:
            lines.extend(["", "Constants", "---------"])
            for variable in sorted(const_dict, key=lambda item: item.id):
                lines.append("{} = {}".format(
                    variable.id, self._model_text(const_dict[variable])
                ))

        lines.extend(["", "Variables", "---------"])
        for variable in sorted(cont_var_dict, key=lambda item: item.id):
            lines.append("{}: {}".format(
                variable.id, self._range_text(cont_var_dict[variable])
            ))

        if init is not None:
            lines.extend([
                "",
                "Initial condition",
                "-----------------",
                self._model_text(init),
            ])

        for index, module in enumerate(ordered_modules):
            start_time = self._assignment_value(assignment, variable_points[index])
            end_time = self._assignment_value(assignment, variable_points[index + 1])
            lines.extend([
                "",
                "Bound {}".format(index),
                "{}".format("-" * (6 + len(str(index)))),
                "time: {} -> {}".format(start_time, end_time),
                "mode: {}".format(self._model_text(module["mode"])),
                "",
                "invariant:",
                "  {}".format(self._model_text(module["inv"])),
                "",
                "flow:",
            ])

            dynamics = module["flow"]
            for variable, expression in zip(dynamics.vars, dynamics.exps):
                if isinstance(dynamics, Ode):
                    lhs = "d/dt[{}]".format(variable.id)
                else:
                    lhs = "{}(t)".format(variable.id)
                lines.append("  {} = {}".format(lhs, self._model_text(expression)))

            lines.extend(["", "state:"])
            for variable in sorted(cont_var_dict, key=lambda item: item.id):
                start_value, end_value = cont_values[variable.id][index]
                lines.append("  {}: {} -> {}".format(
                    variable.id, start_value, end_value
                ))

            if index < len(ordered_modules) - 1:
                lines.extend([
                    "",
                    "next mode: {}".format(
                        self._model_text(ordered_modules[index + 1]["mode"])
                    ),
                    "jump candidates:",
                ])
                jumps = module["jump"]
                if jumps:
                    for guard, reset in jumps.items():
                        lines.append("  {} => {}".format(
                            self._model_text(guard), self._model_text(reset)
                        ))
                else:
                    lines.append("  (none)")

        output_path = "{}.txt".format(file_name)
        with open(output_path, "w", encoding="utf-8") as output_file_handle:
            output_file_handle.write("\n".join(lines) + "\n")
        print("write counterexample text: \'{}\'".format(output_path))

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
