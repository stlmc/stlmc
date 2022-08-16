from typing import Dict, Set

from .aux import literals, print_bound, depth2bound
from ..algorithm import Algorithm, FormulaStack, PathGenerator
from ..runner import SmtSolverRunner
from ...constraints.aux.operations import Substitution, get_vars
from ...constraints.constraints import *
from ...encoding.smt.goal.aux import is_chi, get_hash, get_chi_depth, symbolic_sup, symbolic_inf
from ...encoding.smt.goal.stl import StlGoal
from ...encoding.smt.model.aux import indexed_var_t
from ...encoding.smt.model.stlmc_model import STLmcModel
from ...objects.configuration import Configuration
from ...objects.goal import Goal
from ...objects.model import Model
from ...solver.abstract_solver import SMTSolver
from ...solver.assignment import Assignment
from ...solver.z3 import Z3Solver
from ...util.printer import pprint


class TwoStepAlgorithm(Algorithm):
    def __init__(self, config: Configuration, runner: SmtSolverRunner):
        self._config = config
        self._scenario_solver = Z3Solver(config)
        self._minimize_solver = Z3Solver(config)
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
        self._clear()
        s_solver = self._scenario_solver
        m_solver = self._minimize_solver
        p_runner = self._runner
        f_stack = FormulaStack()
        m_stack = FormulaStack()

        rf = SmtTwoStepPathGenerator(model, goal, m_solver)
        s_solver.reset()
        m_solver.reset()

        common_section = self._config.get_section("common")
        bound = int(common_section.get_value("bound"))

        cl = set()
        num_scenarios_at_bound = list()

        for b in range(bound + 1):
            print("bound : {}".format(b))
            # generate formulas
            model_c, model_c_final = next(model.encode())
            goal_c, goal_c_final = next(goal.encode())

            # add current final
            s_solver.push()
            s_solver.add(And([model_c_final, goal_c_final]))
            f_stack.push(model_c_final, goal_c_final)

            mc_f_literals = literals(model_c_final)
            gc_f_literals = literals(goal_c_final)
            cl.update(mc_f_literals)
            cl.update(gc_f_literals)

            counter = 0
            # m_solver
            m_solver.add(Not(And([f_stack.get_formula(), Bool("&u{}".format(counter))])))
            m_stack.push(Not(And([f_stack.get_formula(), Bool("&u{}".format(counter))])))
            m_solver.push()
            m_solver.add(Bool("&u{}".format(counter)))
            m_stack.push(Bool("&u{}".format(counter)))
            # pprint(Not(And([f_stack.get_formula(), Bool("&u0")])), 0)
            scenarios = list()

            num_s = 0
            print("scenarios @ {}:".format(b))
            while s_solver.check_sat() == SMTSolver.sat:
                num_s += 1
                assn = s_solver.make_assignment()
                print(assn)

                pprint(m_stack.get_formula(), 0)
                path = rf.make_path(cl, assn)
                r_path = rf.refine(path, assn)
                print("  scenario#{} @ bound {}".format(num_s, b))

                p_runner.run(solver, r_path, model)
                r, m = p_runner.check_sat()
                if r == SMTSolver.sat:
                    num_scenarios_at_bound.append(num_s)
                    print_bound(num_scenarios_at_bound)
                    return "False", 0.0, b, m

                s_solver.add(Not(path))
                m_solver.pop()
                m_stack.pop()
                m_solver.add(Bool("&u{}".format(counter)) == And([Not(path), Bool("&u{}".format(counter + 1))]))
                m_stack.push(Bool("&u{}".format(counter)) == And([Not(path), Bool("&u{}".format(counter + 1))]))
                m_solver.push()
                counter += 1
                m_solver.add(Bool("&u{}".format(counter)))
                m_stack.push(Bool("&u{}".format(counter)))
                scenarios.append(path)

            num_scenarios_at_bound.append(num_s)

            r, m = p_runner.wait_and_check_sat()
            if r == SMTSolver.sat:
                print_bound(num_scenarios_at_bound)
                return "False", 0.0, b, m

            # prepare for the next bound
            s_solver.pop()
            f_stack.pop()
            cl.difference_update(mc_f_literals)
            cl.difference_update(gc_f_literals)

            s_solver.add(And([model_c, goal_c]))
            f_stack.push(model_c, goal_c)
            cl.update(literals(model_c))
            cl.update(literals(goal_c))

        print_bound(num_scenarios_at_bound)

        return "True", 0.0, bound, dict()

    def _clear(self):
        self._scenario_solver.reset()
        self._minimize_solver.reset()


class SmtTwoStepPathGenerator(PathGenerator):
    def __init__(self, model: STLmcModel, goal: StlGoal, minimize_solver: SMTSolver):
        self._model = model
        self._goal = goal
        self._m_solver = minimize_solver
        self._hash_dict: Dict[hash, Formula] = self._sub_formula_hash_dict()
        self._path_literals = set()

    def make_path(self, path_literals: Set, assn: Assignment):
        # update path clause
        self._path_literals = path_literals
        for lit in self._path_literals:
            print(lit)
        print("============")
        return self._make_path_formula(assn)

    def refine(self, path: Formula, assn: Assignment):
        # update path clause
        p_f = self._refine_model_related(path)
        t_c = self._refine_goal_related(p_f, assn)
        return t_c

    def _make_path_formula(self, assn: Assignment):
        true, false = self._make_path_literals(assn)
        p_c = self._minimize_literals(true, false)

        return And(p_c)

    def _make_path_literals(self, assn: Assignment):
        true_literals = set()
        false_literals = set()
        # get intermediate variables
        b_inter_vs = self._get_intermediate_variables(assn)

        for literal in self._path_literals:
            v_s = get_vars(literal)
            if len(v_s.intersection(b_inter_vs)) == 0:
                val = assn.eval(literal)
                if val == Assignment.true:
                    true_literals.add(literal)
                elif val == Assignment.false:
                    false_literals.add(literal)
                # else:
                #     print("don't care")
        return true_literals, false_literals

    def _get_intermediate_variables(self, assn):
        bool_intermediate_vs = set()
        for v in assn:
            if is_chi(v):
                h = get_hash(v)
                f = self._hash_dict[h]
                if not isinstance(f, Proposition):
                    bool_intermediate_vs.add(v)
        return bool_intermediate_vs

    def _minimize_literals(self, true_literals: Set[Formula], false_literals: Set[Formula]):
        track_dict = dict()
        true = BoolVal("True")
        false = BoolVal("False")

        self._m_solver.push()

        print()

        for index, c in enumerate(true_literals):
            track_id = "&minimize@true#{}".format(index)
            self._m_solver.assert_and_track(c == true, track_id)
            track_dict[track_id] = c == true
            print("{} --> {}".format(track_id, c == true))

        for index, c in enumerate(false_literals):
            track_id = "&minimize@false#{}".format(index)
            self._m_solver.assert_and_track(c == false, track_id)
            track_dict[track_id] = c == false
            print("{} --> {}".format(track_id, c == false))

        r = self._m_solver.check_sat()
        print("  path minimizer: {}".format(r))
        unsat_core = self._m_solver.unsat_core()
        # print(unsat_core)

        minimized = set()
        for track_id in track_dict:
            if track_id in unsat_core:
                minimized.add(track_dict[track_id])

        self._m_solver.pop()
        return list(minimized)

    def _refine_model_related(self, path_formula: Formula):
        # refine forall and integral
        abs_dict = self._model.get_abstraction()

        # build substitution
        subst = Substitution()
        for v in abs_dict:
            subst.add(v, abs_dict[v])

        return subst.substitute(path_formula)

    def _refine_goal_related(self, path_formula: Formula, assn: Assignment):
        goal_chi = self._get_goal_chi(assn)

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

    def _get_goal_chi(self, assn):
        goal_chi = set()
        for v in assn:
            if is_chi(v):
                h = get_hash(v)
                f = self._hash_dict[h]
                if isinstance(f, Proposition):
                    goal_chi.add((v, f))
        return goal_chi

    def _sub_formula_hash_dict(self):
        sub_fs = self._goal.sub_formulas

        hash_dict = dict()
        for f in sub_fs:
            hash_dict[hash(f)] = f
        return hash_dict
