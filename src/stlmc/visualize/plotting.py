"""Bokeh construction for sampled state and robustness data."""

import itertools
from typing import Dict, List, Set

from bokeh.models import CrosshairTool, DataRange1d, HoverTool, Legend
from bokeh.palettes import Dark2_5 as palette
from bokeh.plotting import column, figure

from ..constraints.constraints import Variable
from .grouping import flatten, pairwise_disjoint_check, split_groups


def build_plot(point_samples, robustness_dict, time_samples_list,
               formula_id_dict, formula_label: str, delta: float,
               user_defined_groups: Dict[int, Set[str]]):
    user_defined_groups_list = list(user_defined_groups.values())
    robust_variables = set()
    for f in robustness_dict:
        robust_variables.add("{}_{}".format(formula_label, formula_id_dict[f]))
    
    v_names: List[Variable] = list(sorted(point_samples.keys(), key=lambda _v: _v.id))
    v_name_dict: Dict[str, Variable] = dict()
    
    for v in point_samples:
        v_name_dict[v.id] = v
    
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
    return column(children=[*main_list, *rob_list], sizing_mode="scale_both")


__all__ = ["build_plot"]
