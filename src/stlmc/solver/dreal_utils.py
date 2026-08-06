from typing import List

from ..objects.configuration import Section


def get_dreal_solver_args(dreal_section: Section) -> List[str]:
    """Build dReal CLI arguments from the optional dreal configuration values."""
    option_names = {
        "precision": "--precision",
        "ode-order": "--ode-order",
        "ode-step": "--ode-step",
    }
    args = []
    for config_name, option_name in option_names.items():
        if dreal_section.is_argument_in(config_name):
            value = dreal_section.get_value(config_name)
            if value != "":
                args.extend([option_name, value])
    return args
