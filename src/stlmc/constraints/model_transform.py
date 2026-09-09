"""Instantiate model variables, invariants, and dynamics at a bound."""

from functools import singledispatch

from .constraints import (
    And, BinaryFormula, Bool, Formula, Function, Int, Ode, Or, Real,
)
from .substitution import substitution


def make_dict(bound, mode_dict, cont_dict, constant_dict, suffix=""):
    result = {}
    variable_types = {"bool": Bool, "int": Int, "real": Real}
    for mode_var in mode_dict.values():
        result[mode_var] = variable_types[mode_var.type](
            mode_var.id + "_" + str(bound)
        )
    for cont_var in cont_dict:
        result[cont_var] = Real(cont_var.id + "_" + str(bound) + suffix)
    result.update(constant_dict)
    return result


@singledispatch
def make_dictionary_for_invariant(
        cur_inv_const: Formula, inv_prop_dict: dict):
    return cur_inv_const, inv_prop_dict


def _abstract_invariant_children(cur_inv_const, inv_prop_dict):
    children = []
    for const in cur_inv_const.children:
        formula, new_dict = make_dictionary_for_invariant(const, inv_prop_dict)
        children.append(formula)
        inv_prop_dict.update(new_dict)
    return type(cur_inv_const)(children), inv_prop_dict


make_dictionary_for_invariant.register(And)(_abstract_invariant_children)
make_dictionary_for_invariant.register(Or)(_abstract_invariant_children)


@make_dictionary_for_invariant.register(BinaryFormula)
def _(cur_inv_const: BinaryFormula, inv_prop_dict: dict):
    new_var = Bool("invAtomicID_" + str(len(inv_prop_dict) + 1))
    inv_prop_dict[new_var] = cur_inv_const
    return new_var, inv_prop_dict


def _dynamics_substitutions(bound, mode_var_dict, range_dict, constant_dict):
    expression_mapping = make_dict(
        bound, mode_var_dict, range_dict, constant_dict, "_0"
    )
    variable_mapping = make_dict(bound, {}, range_dict, {}, "_0_t")
    return expression_mapping, variable_mapping


@singledispatch
def make_new_dynamics(
        dyn: Ode, bound, mode_var_dict, range_dict, constant_dict):
    expression_mapping, variable_mapping = _dynamics_substitutions(
        bound, mode_var_dict, range_dict, constant_dict
    )
    expression_mapping[Real("time")] = Real("tau_" + str(bound + 1))
    return Ode(
        [substitution(var, variable_mapping) for var in dyn.vars],
        [substitution(exp, expression_mapping) for exp in dyn.exps],
    )


@make_new_dynamics.register(Function)
def _(dyn: Function, bound, mode_var_dict, range_dict, constant_dict):
    expression_mapping, variable_mapping = _dynamics_substitutions(
        bound, mode_var_dict, range_dict, constant_dict
    )
    expression_mapping[Real("time")] = (
        Real("tau_" + str(bound + 1)) - Real("tau_" + str(bound))
    )
    return Function(
        [substitution(var, variable_mapping) for var in dyn.vars],
        [substitution(exp, expression_mapping) for exp in dyn.exps],
    )
