"""Human-readable witness and counterexample artifact output."""

from ..constraints.constraints import Ode
from ..constraints.operations import substitution
from .projection import Projector, continuous_values


def model_text(value):
    return str(value).replace("##$%^&$%^&##'", "'")


def assignment_value(assignment, variable):
    value = assignment.get(variable)
    return value.value if value is not None else "?"


def range_text(value_range):
    left_closed, left, right, right_closed = value_range
    return "{}{}, {}{}".format(
        "[" if left_closed else "(", left, right,
        "]" if right_closed else ")",
    )


def write_counterexample_text(
        file_name, assignment, modules, mode_var_dict, propositions,
        continuous_variables, proposition_dict, formula, formula_label, delta,
        init=None, const_dict=None):
    projector = Projector(
        assignment, mode_var_dict, propositions, modules
    )
    ordered_modules = projector.get_ordered_modules()
    max_bound = projector.get_max_bound()
    variable_points = projector.get_variable_points()
    endpoint_values = continuous_values(
        assignment, continuous_variables, max_bound
    )
    expanded_formula = substitution(formula, proposition_dict)

    heading = "Witness" if file_name.endswith(".witness") else "Counterexample"
    lines = [
        heading, "=" * len(heading), "",
        "goal: {}".format(formula_label),
        "formula: {}".format(model_text(expanded_formula)),
        "bound: {}".format(max_bound), "delta: {}".format(delta),
    ]
    if const_dict:
        lines.extend(["", "Constants", "---------"])
        for variable in sorted(const_dict, key=lambda item: item.id):
            lines.append("{} = {}".format(
                variable.id, model_text(const_dict[variable])
            ))

    lines.extend(["", "Variables", "---------"])
    for variable in sorted(continuous_variables, key=lambda item: item.id):
        lines.append("{}: {}".format(
            variable.id, range_text(continuous_variables[variable])
        ))
    if init is not None:
        lines.extend([
            "", "Initial condition", "-----------------", model_text(init),
        ])

    for index, module in enumerate(ordered_modules):
        lines.extend([
            "", "Bound {}".format(index), "-" * (6 + len(str(index))),
            "time: {} -> {}".format(
                assignment_value(assignment, variable_points[index]),
                assignment_value(assignment, variable_points[index + 1]),
            ),
            "mode: {}".format(model_text(module["mode"])), "",
            "invariant:", "  {}".format(model_text(module["inv"])), "",
            "flow:",
        ])
        dynamics = module["flow"]
        for variable, expression in zip(dynamics.vars, dynamics.exps):
            lhs = (
                "d/dt[{}]".format(variable.id)
                if isinstance(dynamics, Ode)
                else "{}(t)".format(variable.id)
            )
            lines.append("  {} = {}".format(lhs, model_text(expression)))

        lines.extend(["", "state:"])
        for variable in sorted(continuous_variables, key=lambda item: item.id):
            start, end = endpoint_values[variable.id][index]
            lines.append("  {}: {} -> {}".format(variable.id, start, end))

        if index < len(ordered_modules) - 1:
            lines.extend([
                "", "next mode: {}".format(
                    model_text(ordered_modules[index + 1]["mode"])
                ),
                "jump candidates:",
            ])
            jumps = module["jump"]
            if jumps:
                lines.extend(
                    "  {} => {}".format(model_text(guard), model_text(reset))
                    for guard, reset in jumps.items()
                )
            else:
                lines.append("  (none)")

    output_path = "{}.txt".format(file_name)
    with open(output_path, "w", encoding="utf-8") as output:
        output.write("\n".join(lines) + "\n")
    print("write counterexample text: '{}'".format(output_path))


__all__ = [
    "assignment_value", "model_text", "range_text",
    "write_counterexample_text",
]
