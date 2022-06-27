from typing import *

import z3
from ..solver.z3 import z3Obj

from ..constraints.constraints import *
from ..constraints.operations import *
from ..objects.model import Model


class StaticLearner:
    def __init__(self, model: Model, formula: Formula):
        self.model = model
        self.formula = formula

        self.continuous_vars = {v for v in self.model.range_dict}
        self.mode_vars = {self.model.mode_var_dict[v] for v in self.model.mode_var_dict}
        self.contradiction_dict: Dict[int, Set[Formula]] = dict()

    def get_contradiction_upto(self, bound: int, org_const):
        children = set()
        bounds = list(sorted(self.contradiction_dict.keys()))
        for b in bounds:
            if b <= bound:
                for chi in self.contradiction_dict[b]:
                    if clause(chi).issubset(org_const):
                        children.add(chi)
        return And(list(children))

    def generate_learned_clause(self, bound: int, delta: float):
        model_clause = set()

        model_clause.update(clause(self.model.init))
        # self.model.modules

        for module in self.model.modules:
            model_clause.update(clause(module["mode"]))
            model_clause.update(clause(module["inv"]))
            jumps = module["jump"]
            for cond in jumps:
                model_clause.update(clause(cond))

        neg_formula = reduce_not(Not(self.formula))
        neg_relaxed_formula = relaxing(neg_formula, delta)
        relaxed_formula = relaxing(self.formula, delta)

        stl_clause = clause(neg_relaxed_formula)
        stl_clause.update(clause(relaxed_formula))


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
                is_real = isinstance(mode_var, Real)
                is_int = isinstance(mode_var, Int)

                if not is_real or not is_int:
                    continue

                if is_real:
                    mode_rename_dict_at[mode_var] = Real("{}_{}".format(mode_var.id, i))
                else:
                    mode_rename_dict_at[mode_var] = Int("{}_{}".format(mode_var.id, i))
            assert i not in mode_rename_dict
            mode_rename_dict[i] = mode_rename_dict_at

        contra_solver = z3.SolverFor("QF_LRA")
        for i in range(0, int(bound) + 1):
            assert i in cont_rename_dict_0
            assert i in cont_rename_dict_t
            assert i in mode_rename_dict

            renamed_clause = set()
            for c in stl_clause:
                renamed_clause.add(substitution(c, cont_rename_dict_0[i]))
                renamed_clause.add(substitution(c, cont_rename_dict_t[i]))
                renamed_clause.add(substitution(c, mode_rename_dict[i]))

            for c in model_clause:
                renamed_clause.add(substitution(c, cont_rename_dict_0[i]))
                renamed_clause.add(substitution(c, cont_rename_dict_t[i]))
                renamed_clause.add(substitution(c, mode_rename_dict[i]))

            renamed_clause.difference_update(stl_clause)
            renamed_clause.difference_update(model_clause)

            potentials = set(combinations(renamed_clause, 2))
            contradiction_pairs = set()
            for (c1, c2) in potentials:
                contra_solver.push()
                contra_solver.add(z3Obj(And([c1, c2])))
                result = contra_solver.check()

                # contradiction
                if result.r == z3.Z3_L_FALSE:
                    child = And([c1, c2])
                    contradiction_pairs.add(Not(child))

                contra_solver.pop()
            self.contradiction_dict[i] = contradiction_pairs

