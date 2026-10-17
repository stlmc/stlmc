from itertools import combinations
from typing import Dict, Tuple

from ..constraints.constraints import And, Formula, Int, Not, Real, Variable
from ..constraints.logical_normalization import reduce_not
from ..constraints.encoding_helpers import clause, ordered_clause
from ..constraints.robustness_transform import relaxing
from ..constraints.substitution import substitution
from ..objects.model import Model
from ..solver.abstract_solver import IncrementalFormulaSolver, SolverStatus


def renamed_discrete_variable(variable: Variable, bound: int):
    """Return the bound-specific numeric variable used by static learning."""
    if isinstance(variable, Real):
        return Real("{}_{}".format(variable.id, bound))
    if isinstance(variable, Int):
        return Int("{}_{}".format(variable.id, bound))
    return None


class StaticLearner:
    def __init__(self, model: Model, formula: Formula, solver_factory):
        self.model = model
        self.formula = formula
        self.solver_factory = solver_factory

        self.continuous_vars = tuple(self.model.range_dict)
        self.mode_vars = tuple(self.model.mode_var_dict.values())
        self.contradiction_dict: Dict[int, Tuple[Formula, ...]] = dict()

    def get_contradiction_upto(self, bound: int, org_const):
        children = dict()
        bounds = list(sorted(self.contradiction_dict.keys()))
        for b in bounds:
            if b <= bound:
                for chi in self.contradiction_dict[b]:
                    if clause(chi).issubset(org_const):
                        children[chi] = None
        return And(list(children))

    def generate_learned_clause(self, bound: int, delta: float):
        model_clause = dict.fromkeys(ordered_clause(self.model.init))

        # self.model.modules

        for module in self.model.modules:
            model_clause.update(dict.fromkeys(ordered_clause(module["mode"])))
            model_clause.update(dict.fromkeys(ordered_clause(module["inv"])))
            jumps = module["jump"]
            for cond in jumps:
                model_clause.update(dict.fromkeys(ordered_clause(cond)))

        neg_formula = reduce_not(Not(self.formula))
        neg_relaxed_formula = relaxing(neg_formula, delta)
        relaxed_formula = relaxing(self.formula, delta)

        stl_clause = dict.fromkeys(ordered_clause(neg_relaxed_formula))
        stl_clause.update(dict.fromkeys(ordered_clause(relaxed_formula)))


        cont_rename_dict_0 = dict()
        cont_rename_dict_t = dict()
        mode_rename_dict = dict()
        for i in range(0, int(bound) + 1):
            cont_rename_dict_0_at = dict()
            cont_rename_dict_t_at = dict()

            for cont_var in self.continuous_vars:
                is_real = isinstance(cont_var, Real)
                is_int = isinstance(cont_var, Int)

                assert (is_real and not is_int) or (not is_real and is_int)

                if is_real:
                    cont_rename_dict_0_at[cont_var] = Real("{}_{}_0".format(cont_var.id, i))
                    cont_rename_dict_t_at[cont_var] = Real("{}_{}_t".format(cont_var.id, i))
                else:
                    cont_rename_dict_0_at[cont_var] = Int("{}_{}_0".format(cont_var.id, i))
                    cont_rename_dict_t_at[cont_var] = Int("{}_{}_t".format(cont_var.id, i))

            assert i not in cont_rename_dict_0
            assert i not in cont_rename_dict_t
            cont_rename_dict_0[i] = cont_rename_dict_0_at
            cont_rename_dict_t[i] = cont_rename_dict_t_at

            mode_rename_dict_at = dict()
            for mode_var in self.mode_vars:
                renamed = renamed_discrete_variable(mode_var, i)
                if renamed is not None:
                    mode_rename_dict_at[mode_var] = renamed
            assert i not in mode_rename_dict
            mode_rename_dict[i] = mode_rename_dict_at

        contra_solver: IncrementalFormulaSolver = self.solver_factory("QF_LRA")
        for i in range(0, int(bound) + 1):
            assert i in cont_rename_dict_0
            assert i in cont_rename_dict_t
            assert i in mode_rename_dict

            renamed_clause = dict()
            for c in stl_clause:
                renamed_clause[substitution(c, cont_rename_dict_0[i])] = None
                renamed_clause[substitution(c, cont_rename_dict_t[i])] = None
                renamed_clause[substitution(c, mode_rename_dict[i])] = None

            for c in model_clause:
                renamed_clause[substitution(c, cont_rename_dict_0[i])] = None
                renamed_clause[substitution(c, cont_rename_dict_t[i])] = None
                renamed_clause[substitution(c, mode_rename_dict[i])] = None

            for c in (*stl_clause, *model_clause):
                renamed_clause.pop(c, None)

            # combinations already emits each pair once. Fix both pair
            # orientation and incremental solver query order across seeds.
            potentials = combinations(renamed_clause, 2)
            contradiction_pairs = dict()
            for (c1, c2) in potentials:
                contra_solver.push()
                contra_solver.add(And([c1, c2]))
                result = contra_solver.check()

                # contradiction
                if result == SolverStatus.UNSAT:
                    child = And([c1, c2])
                    contradiction_pairs[Not(child)] = None

                contra_solver.pop()
            self.contradiction_dict[i] = tuple(contradiction_pairs)
