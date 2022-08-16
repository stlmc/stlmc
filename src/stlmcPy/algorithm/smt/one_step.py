from typing import Dict, Set

from .aux import literals, depth2bound
from ..algorithm import Algorithm, PathGenerator, FormulaStack
from ..runner import SmtSolverRunner
from ...constraints.aux.operations import Substitution, get_vars
from ...constraints.constraints import *
from ...encoding.smt.goal.aux import is_chi, get_hash, symbolic_sup, symbolic_inf, get_chi_depth
from ...encoding.smt.goal.stl import StlGoal
from ...encoding.smt.model.aux import indexed_var_t
from ...encoding.smt.model.stlmc_model import STLmcModel
from ...objects.configuration import Configuration
from ...objects.goal import Goal
from ...objects.model import Model
from ...solver.abstract_solver import SMTSolver
from ...util.printer import pprint


class OneStepAlgorithm(Algorithm):
    def __init__(self, config: Configuration, runner: SmtSolverRunner):
        self._config = config
        self._runner = runner

    def run(self, model: Model, goal: Goal, solver: SMTSolver):
        if isinstance(model, STLmcModel) and isinstance(goal, StlGoal):
            return self._smt_check_sat(model, goal, solver)
        else:
            if not isinstance(model, STLmcModel):
                raise Exception("wrong model type is given")

            if not isinstance(goal, StlGoal):
                raise Exception("wrong goal type is given")

    def _smt_check_sat(self, model: STLmcModel, goal: StlGoal, solver: SMTSolver):
        solver.reset()

        p_runner = self._runner
        f_stack = FormulaStack()

        rf = SmtOneStepPathGenerator(model, goal)

        common_section = self._config.get_section("common")
        bound = int(common_section.get_value("bound"))

        for b in range(bound + 1):
            print("bound : {}".format(b))
            # generate formulas
            model_c, model_c_final = next(model.encode())
            goal_c, goal_c_final = next(goal.encode())

            # add current final
            solver.push()
            solver.add(And([model_c_final, goal_c_final]))
            f_stack.push(model_c_final, goal_c_final)

            r_path = rf.refine(f_stack.get_formula())
            pprint(r_path, 0)

            p_runner.run(solver, r_path, model)
            r, m = p_runner.check_sat()
            if r == SMTSolver.sat:
                return "False", 0.0, b, m

            # prepare for the next bound
            solver.pop()
            f_stack.pop()

            solver.add(And([model_c, goal_c]))
            f_stack.push(model_c, goal_c)
        return "True", 0.0, bound, dict()


class SmtOneStepPathGenerator(PathGenerator):
    def __init__(self, model: STLmcModel, goal: StlGoal):
        self._model = model
        self._goal = goal
        self._hash_dict: Dict[hash, Formula] = self._sub_formula_hash_dict()
        self._path_literals = set()

    def refine(self, path_formula: Formula):
        p_f = self._refine_model_related(path_formula)
        t_c = self._refine_goal_related(p_f)
        return t_c

    def _refine_model_related(self, path_formula: Formula):
        # refine forall and integral
        abs_dict = self._model.get_abstraction()

        # build substitution
        subst = Substitution()
        for v in abs_dict:
            subst.add(v, abs_dict[v])

        return subst.substitute(path_formula)

    def _refine_goal_related(self, path_formula: Formula):
        goal_chi = self._get_proposition_literals(path_formula)

        goal_refinement = list()
        for g_chi, f in goal_chi:
            depth = get_chi_depth(g_chi)
            bound = depth2bound(depth)
            is_mode = depth % 2 == 0

            if is_mode:
                # currently we do not use current mode number
                const = Forall(-1, symbolic_sup(depth), symbolic_inf(depth), f)
                goal_refinement.append(g_chi == const)
            else:
                f_vs = get_vars(f)

                # build substitution
                subst_0 = Substitution()

                for v in f_vs:
                    # do not consider initial transition
                    if bound > 0:
                        subst_0.add(v, indexed_var_t(v, bound - 1))

                inv = subst_0.substitute(f)
                goal_refinement.append(g_chi == inv)

        return And([path_formula, And(goal_refinement)])

    def _get_proposition_literals(self, path_formula: Formula):
        bool_proposition_vs = set()
        var_set = get_vars(path_formula)
        for v in var_set:
            if is_chi(v):
                h = get_hash(v)
                f = self._hash_dict[h]
                if isinstance(f, Proposition):
                    bool_proposition_vs.add((v, f))
        return bool_proposition_vs

    def _sub_formula_hash_dict(self):
        sub_fs = self._goal.sub_formulas

        hash_dict = dict()
        for f in sub_fs:
            hash_dict[hash(f)] = f
        return hash_dict
