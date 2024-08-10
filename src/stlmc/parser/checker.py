import os.path
from functools import reduce
from typing import List

from ..constraints.constraints import *
from ..constraints.operations import get_vars
from ..objects.configuration import Configuration
from ..objects.model import StlMC


def is_dynamics_constant(flows: Dynamics):
    variables = flows.vars
    for index, variable in enumerate(variables):
        exp = flows.exps[index]
        if not isinstance(exp, Constant):
            return False
    return True


def is_model_dynamics_constant(stlmc_model: StlMC):
    # constant
    for mode in stlmc_model.modules:
        if not is_dynamics_constant(mode["flow"]):
            return False
    return True


def is_dynamics_polynomial(flows: Dynamics):
    if isinstance(flows, Function):
        return True

    variables = flows.vars
    for index, variable in enumerate(variables):
        exp = flows.exps[index]
        exp_vars = get_vars(exp)
        exp_vars.discard(variable)
        if len(exp_vars) > 0:
            return True
    return False


def is_model_dynamics_polynomial(stlmc_model: StlMC):
    for mode in stlmc_model.modules:
        if not is_dynamics_polynomial(mode["flow"]):
            return False
    return True


def check_dynamics(stlmc_model: StlMC):
    if is_model_dynamics_constant(stlmc_model):
        return "constant"

    if is_model_dynamics_polynomial(stlmc_model):
        return "polynomial"

    is_polynomial = False
    is_ode = False

    for mode in stlmc_model.modules:
        flows = mode["flow"]
        variables = flows.vars

        trigonometric = [Sin, Cos, Tan, Arcsin, Arccos, Arctan, Sqrt]

        for index, variable in enumerate(variables):
            exp = flows.exps[index]
            if exp.__class__ in trigonometric:
                is_ode = True
                break

    if not is_ode:
        is_polynomial = True

    if is_ode:
        return "ode"

    if is_polynomial:
        return "polynomial"


def check_validity(config: Configuration):
    common_section = config.get_section("common")
    underlying_solver = common_section.get_value("solver")
    for section_name in config.type_check_dict:
        section = config.get_section(section_name)
        my_check = config.type_check_dict[section_name]
        for arg_name in section.arguments:
            arg_val = section.arguments[arg_name]
            for arg_type, ty in my_check:
                if arg_type == arg_name:
                    quote_removed_val = arg_val.replace("\"", "")
                    if ty == "string":
                        continue
                    elif ty == "integer" or ty == "float":
                        try:
                            if ty == "integer":
                                int(quote_removed_val)
                            else:
                                float(quote_removed_val)
                        except ValueError:
                            raise ValueError("\"{}\" is not a valid parameter for the argument \"{}\", "
                                             "only {} value is allowed".format(quote_removed_val, arg_name, ty))
                    elif isinstance(ty, frozenset):
                        if quote_removed_val not in ty:
                            raise ValueError("\"{}\" is not a valid parameter for the argument \"{}\" "
                                             "(please provide one of {{{}}})"
                                             .format(quote_removed_val, arg_name, " , ".join(ty)))
                    elif ty == "path" and underlying_solver == "dreal":
                        if not os.path.exists(quote_removed_val):
                            raise ValueError("\"{}\" is not a valid executable path containing dReal executable"
                                             .format(quote_removed_val))
