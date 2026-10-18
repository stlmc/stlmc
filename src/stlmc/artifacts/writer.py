from pathlib import Path

from ..constraints.substitution import substitution
from .formula_index import index_subformulas
from .codec import dump_artifact


def write_verification_artifacts(
        model_file, bound, label, solver_name, reachability,
        assignment, model, proposition_definitions, goal, threshold):
    """Persist a witness/counterexample and its visualization configuration."""
    output_name = "{}_b{}_{}_{}".format(
        Path(model_file).stem, bound, label, solver_name
    )
    suffix = "witness" if reachability else "counterexample"
    artifact_path = "{}.{}".format(output_name, suffix)
    config_path = "{}.cfg".format(output_name)

    dump_artifact(artifact_path, (
        assignment, model.modules, model.mode_var_dict, model.prop_dict,
        model.range_dict, proposition_definitions, goal.get_formula(),
        label, float(threshold), model.init, model.const_dict,
    ), metadata={
        "kind": suffix,
        "model": Path(model_file).name,
        "bound": bound,
        "goal": label,
        "solver": solver_name,
    })

    expanded_formula = substitution(
        goal.get_formula(), proposition_definitions
    )
    subformulas, formula_ids = index_subformulas(expanded_formula)
    lines = [
        "{",
        "# state variables: {}".format(
            " , ".join(variable.id for variable in model.range_dict)
        ),
    ]
    lines.extend(sorted(
        "# {}_{} ---> {}".format(label, formula_ids[formula], formula)
        for formula in subformulas
    ))
    lines.extend(["output = html # pdf", "group {", "}", "}"])
    Path(config_path).write_text("\n".join(lines), encoding="utf-8")
    return artifact_path, config_path
