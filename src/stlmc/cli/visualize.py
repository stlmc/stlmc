from __future__ import annotations

import os
import re
import argparse
import subprocess
from functools import reduce
from typing import *

def svg_out(main_figure: figure, rob_figure: figure):
    from bokeh.io import export_svg
    from bokeh.models import DataRange1d

    # assert visualizer.plot is not None
    # assert isinstance(visualizer.plot, Plot)
    # visualizer.plot
    # /.output_backend = "svg"
    main_filename = "state"
    rob_filename = "rob"

    files = [main_filename, rob_filename]

    main_figure.sizing_mode = "fixed"
    main_figure.output_backend = "svg"
    main_figure.width = 2400
    main_figure.height = 1000
    main_figure.legend.label_text_font_size = "90px"
    main_figure.legend.label_width = 15
    main_figure.legend.glyph_width = 60
    main_figure.yaxis.major_label_text_font_size = "125px"
    main_figure.xaxis.major_label_text_font_size = "125px"
    main_figure.title = None
    main_figure.xaxis.axis_label = None
    main_figure.yaxis.axis_label = None
    main_figure.x_range = DataRange1d(start=0.0, bounds='auto')

    rob_figure.sizing_mode = "fixed"
    rob_figure.output_backend = "svg"
    rob_figure.width = 2200
    rob_figure.height = 920
    rob_figure.legend.label_text_font_size = "90px"
    rob_figure.legend.label_width = 15
    rob_figure.legend.glyph_width = 60
    rob_figure.yaxis.major_label_text_font_size = "125px"
    rob_figure.xaxis.major_label_text_font_size = "125px"

    export_svg(main_figure, filename="{}.svg".format(main_filename))
    export_svg(rob_figure, filename="{}.svg".format(rob_filename))


def check_gnuplot():
    result = subprocess.run(["gnuplot", "-V"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    respond = str(result.stdout.decode('utf-8'))
    if "gnuplot" not in respond:
        ValueError("gnuplot is not available (check: \"gnuplot -V\")")


def gnuplot(file_name, 
            user_defined_groups: Dict[int, Set[str]],
            formula_id_dict,
            states: Dict[Variable, List[List[float]]],
            robustness: Dict[Formula, List[List[float]]],
            all_time_samples: List[List[float]], 
            delta, formula_label):
    from ..visualize.visualizer import (
        flatten, formula2latex, pairwise_disjoint_check, split_groups,
    )

    user_defined_groups_list = list(user_defined_groups.values())

    check_gnuplot()
    robust_variables = set()
    formula_dict: Dict[str, Formula] = dict()
    for f in robustness:
        robust_variables.add("{}_{}".format(formula_label, formula_id_dict[f]))
        formula_dict[formula_id_dict[f]] = f

    script = ["set terminal pdfcairo font \"Helvetica, 25\" enhanced size 7,2.6", "set grid",
              "set key font \", 35\"", "set ytics font \", 35\" 5",
              "set datafile missing '-'", "set xtics format \"\""]

    v_names: List[Variable] = list(sorted(states.keys(), key=lambda _v: _v.id))
    blocks = ["# {}".format(" , ".join(map(lambda _v: _v.id, v_names)))]
    for interval, time_samples in enumerate(all_time_samples):
        block = list()
        for time_point_index, time_point in enumerate(time_samples):
            line = [str(time_point)]
            for v in v_names:
                line.append(str(states[v][interval][time_point_index]))
            block.append(" ".join(line))
        blocks.append("\n".join(block))

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

    f = open("state.dat", "w")
    f.write("\n".join(blocks))
    f.close()
    print("write state.dat")

    formula_names = list(robustness.keys())
    formula_names_index: Dict[str, int] = dict()
    for index, formula_name in enumerate(formula_names):
        assert formula_name in formula_id_dict
        formula_names_index["{}_{}".format(formula_label, formula_id_dict[formula_name])] = index

    formula_latex = list(map(lambda _f: formula2latex(_f), formula_names))
    rob_blocks = ["# {}".format(" , ".join(formula_latex))]
    for interval, time_samples in enumerate(all_time_samples):
        block = list()
        for time_point_index, time_point in enumerate(time_samples):
            line = [str(time_point)]
            for f in formula_names:
                line.append(str(robustness[f][interval][time_point_index]))
            block.append(" ".join(line))
        rob_blocks.append("\n".join(block))

    f = open("rob.dat", "w")
    f.write("\n".join(rob_blocks))
    f.close()
    print("write rob.dat")

    pdf_names = list()

    plots = list()
    for g_index, group in enumerate(state_vars):
        plots.clear()
        for v_name in group:
            if v_name not in v_names_index:
                raise ValueError("{} is not a state variable".format(v_name))
            index = v_names_index[v_name]
            plots.append("\"state.dat\" using 1:{} with lines lt 1 lc {} lw 5.2 title \"{}\"".format(index + 2,
                                                                                                     index + 1, v_name))
        if len(plots) > 0:
            script.append("set output 'state_{}.pdf'".format("_".join(sorted(group))))
            script.append("plot {}".format(",\\\n".join(plots)))
            pdf_names.append("'state_{}.pdf'".format("_".join(sorted(group))))

    script.extend(["set arrow from 0,0 to 30,0 nohead lw 2.0 lc black",
                   "set arrow from 0,{} to 30,{} nohead dt \"-\" lw 4.5 lc rgb \"#a52a2a\"".format(delta, delta)])

    for g_index, group in enumerate(robust_vars):
        plots.clear()

        for r_name in group:
            if r_name not in formula_names_index:
                raise ValueError("{} is not a valid subformula name".format(r_name))

            index = formula_names_index[r_name]
            plots.append("\"rob.dat\" using 1:{} with lines lt 1 lc {} lw 5.2 title \"{}\"".format(index + 2,
                                                                                                   index + 1, r_name))
        if len(plots) > 0:
            script.append("set output 'rob_{}.pdf'".format("_".join(sorted(group))))
            script.append("plot {}".format(",\\\n".join(plots)))
            pdf_names.append("'rob_{}.pdf'".format("_".join(sorted(group))))

    f = open("{}.gnu".format(file_name), "w")
    f.write("\n".join(script))
    f.close()

    print("write {}.gnu".format(file_name))

    result = subprocess.run(["gnuplot", "{}.gnu".format(file_name)],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    respond_err = str(result.stderr.decode('utf-8'))
    if respond_err != "":
        ValueError("gnuplot failed to draw ({})".format(respond_err))

    print("write counterexample graphs: {}".format(" , ".join(pdf_names)))



def tuple_type(strings):
    strings = strings.replace("(", "").replace(")", "").replace(" ", "")
    splits = strings.split(",")
    remove_redundant = set()
    for s in splits:
        if s != "":
            remove_redundant.add(s)
    return remove_redundant


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('file', nargs='?', type=str, help="target counterexample data file")
    parser.add_argument('-cfg', metavar='C', type=str,
                        help="set a visualization configuration file (default: \'<file>.cfg\')")
    parser.add_argument("-output", metavar="O", nargs='?', type=str,
                        help="set output format, one of {html, pdf, text} (default: html)")
    args = parser.parse_args()

    try:
        if args.file is None:
            raise ValueError("should provide a counterexample data file")

        if not os.path.exists(args.file):
            raise ValueError("\'{}\' does not exist".format(args.file))

        if os.path.isdir(args.file):
            raise ValueError("\'{}\' is not a file".format(args.file))

        # Visualization dependencies are intentionally loaded after argparse,
        # so `stlmc-vis -h` does not initialize Bokeh, Lark, or STLmc solvers.
        from ..parser.visualize_visitor import VisualizeConfigParser
        from ..visualize.visualizer import Visualizer

        import pickle

        with open(args.file, "rb") as fr:
            data = pickle.load(fr)

        file_name = os.path.basename(args.file).split(".")[0]

        supported_outputs = ["html", "pdf", "text"]

        core_data = data[:9]
        init = data[9] if len(data) > 9 else None
        const_dict = data[10] if len(data) > 10 else None

        if args.output is not None and args.output not in supported_outputs:
            raise ValueError(
                "STLmc visualization script does not support output format {}".format(args.output)
            )

        if args.output == "text":
            visualizer = Visualizer()
            visualizer.write_text(args.file, *core_data, init, const_dict)
            return

        if args.cfg is None:
            args.cfg = "{}.cfg".format(file_name)

        if not os.path.exists(args.cfg):
            raise ValueError("\'{}\' does not exist".format(args.cfg))

        if os.path.isdir(args.cfg):
            raise ValueError("\'{}\' is not a file".format(args.cfg))

        print("read configuration file \'{}\' ... ".format(args.cfg))
        config_parser = VisualizeConfigParser()
        config_parser.read(args.cfg)

        output = config_parser.output
        if args.output:
            output = args.output

        visualizer = Visualizer()
        if output == "html":
            visualizer.generate_plot(*core_data, config_parser.group)
            visualizer.write("{}".format(args.file))

        elif output == "pdf":
            point_samples, robustness_dict, time_samples_list, formula_id_dict, formula_label, delta = visualizer.generate_data(*core_data)
            gnuplot(file_name, config_parser.group, formula_id_dict, point_samples, robustness_dict, time_samples_list, delta, formula_label)

        elif output == "text":
            visualizer.write_text(args.file, *core_data, init, const_dict)

        else:
            if args.output == "" or args.output is None:
                raise ValueError("output format should be given ([pdf, html, text])")
            else:
                raise ValueError("STLmc visualization script dose not support output format {}".format(args.output))
    except ValueError as err:
        print("visualization error: {}".format(err))
