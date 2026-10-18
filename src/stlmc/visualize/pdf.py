"""Headless PDF rendering, independent of Bokeh and external executables."""

from .grouping import flatten, pairwise_disjoint_check, split_groups


def require_matplotlib():
    try:
        from matplotlib.figure import Figure
        from matplotlib.backends.backend_pdf import FigureCanvasPdf
    except (ImportError, OSError) as error:
        raise ValueError(
            "PDF visualization requires Matplotlib. Run: stlmc-installer install --visualize pdf"
        ) from error
    return Figure, FigureCanvasPdf


def write_pdf(file_name, user_defined_groups, formula_id_dict, states,
              robustness, all_time_samples, delta, formula_label):
    Figure, FigureCanvasPdf = require_matplotlib()
    state_names = {variable.id: variable for variable in states}
    robust_names = {"{}_{}".format(formula_label, formula_id_dict[formula]): formula
                    for formula in robustness}
    groups = list(user_defined_groups.values())
    if groups:
        pairwise_disjoint_check(groups)
        state_groups, robust_groups = split_groups(groups, set(state_names), set(robust_names))
        state_groups.append(set(state_names).difference(flatten(state_groups)))
        robust_groups.append(set(robust_names).difference(flatten(robust_groups)))
    else:
        state_groups, robust_groups = [set(state_names)], [set(robust_names)]

    outputs = []
    for prefix, grouped, names, values in (
            ("state", state_groups, state_names, states),
            ("rob", robust_groups, robust_names, robustness)):
        for group in grouped:
            if not group:
                continue
            figure = Figure(figsize=(9, 3.5), layout="constrained")
            canvas = FigureCanvasPdf(figure)
            axes = figure.subplots()
            for name in sorted(group):
                color = None
                # Separate artists prevent interpolation across hybrid resets.
                for index, times in enumerate(all_time_samples):
                    line, = axes.plot(times, values[names[name]][index],
                                      label=name if index == 0 else "_nolegend_",
                                      color=color)
                    color = line.get_color()
            if prefix == "rob":
                axes.axhline(0, color="black", linewidth=1)
                axes.axhline(delta, color="brown", linestyle="--", linewidth=1,
                             label="threshold")
            axes.set_xlabel("time")
            axes.set_ylabel("state" if prefix == "state" else "robustness")
            axes.grid(True)
            axes.legend()
            output = "{}_{}.pdf".format(prefix, "_".join(sorted(group)))
            canvas.print_pdf(output)
            figure.clear()
            outputs.append(output)
    print("write counterexample graphs: {}".format(", ".join(outputs)))
    return outputs
