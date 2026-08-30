import time
from functools import reduce, singledispatch
from typing import *

from ..constraints.operations import *
from ..objects.algorithm import *
from ..objects.configuration import Configuration
from ..objects.goal import Goal, ReachGoal
from ..objects.model import Model
from ..solver.abstract_solver import JobSolver, SolverStatus
from ..constraints.operations import size_of_tree
from ..utils.print import Printer
from ..utils.interrupt import raise_if_interrupted
from ..exceptions import IllegalArgumentError
from .batching import candidate_batch_formula
from .path import PathProvider, SymbolicPathProvider
def is_temporal_definitional(variable) -> bool:
    return (isinstance(variable, Bool)
            and variable.id.startswith(("rho^", "parU^", "parEnd")))


def assert_and_track_assignment(solver, formula: Formula, valuation: BoolVal,
                                track_id: str) -> Eq:
    """Track the exact polarity of a scenario literal and return that literal."""
    literal = Eq(formula, valuation)
    solver.track(literal, track_id)
    return literal


def evaluated_arithmetic_literals(clauses: Set[Formula], real_set: Set[Variable],
                                   model) -> List[Eq]:
    """Return exact truth assignments for clauses determined by real variables."""
    true = BoolVal("True")
    false = BoolVal("False")
    literals = []
    for clause_formula in clauses:
        if get_vars(clause_formula).intersection(real_set):
            valuation = model.eval(clause_formula)
            literals.append(Eq(clause_formula, valuation))
    return literals


def relevant_boolean_abstract_links(boolean_abstract: Dict[Bool, Formula],
                                    roots: Formula,
                                    assignments=None) -> Formula:
    """Keep the dependency closure of abstraction definitions used by roots.

    A definition ``b <-> F`` outside this closure is existentially removable:
    neither ``b`` nor anything depending on it occurs in the refinement.
    """
    abstract_variables = set(boolean_abstract)
    pending = list(get_vars(roots).intersection(abstract_variables))
    relevant = set(pending)
    while pending:
        variable = pending.pop()
        dependencies = get_vars(boolean_abstract[variable]).intersection(
            abstract_variables
        )
        for dependency in dependencies.difference(relevant):
            relevant.add(dependency)
            pending.append(dependency)
    assignments = assignments or {}
    links = []
    for variable in boolean_abstract:
        if variable not in relevant:
            continue
        definition = substitution(boolean_abstract[variable], assignments)
        if variable in assignments:
            if assignments[variable] == BoolVal("True"):
                links.append(definition)
            else:
                # Keep logical negation explicit. reduce_not() rewrites a
                # negated Bool dependency to a distinct complement symbol.
                links.append(Not(definition))
        else:
            links.append(Eq(variable, definition))
    return And(links)


def boolean_core_assignments(formula: Formula) -> Dict[Bool, BoolVal]:
    """Collect explicit Boolean equalities retained in a scenario core."""
    assignments = {}
    pending = [formula]
    while pending:
        current = pending.pop()
        if isinstance(current, And):
            pending.extend(current.children)
            continue
        if not isinstance(current, Eq):
            continue
        if isinstance(current.left, Bool) and isinstance(current.right, BoolVal):
            assignments[current.left] = current.right
        elif isinstance(current.right, Bool) and isinstance(current.left, BoolVal):
            assignments[current.right] = current.left
    return assignments


class TwoStepAlgorithm(Algorithm):
    """Enumerate abstract scenarios and check their continuous refinements."""
    def __init__(self, path_provider: PathProvider = None,
                 scenario_solver_factory=None):
        if scenario_solver_factory is None:
            raise ValueError("scenario_solver_factory is required")
        self.scenario_solver_factory = scenario_solver_factory
        self.scenario_solver = scenario_solver_factory("QF_LRA")
        self.minimize_solver = scenario_solver_factory("QF_LRA")

        self.clause_set: Set[Formula] = set()
        self.run_queue = set()
        self.runner = None
        self.debug_name = ""
        self.last_scenario_count = 0
        self.path_provider = path_provider or SymbolicPathProvider()

    def clear(self):
        self.scenario_solver = self.scenario_solver_factory("QF_LRA")
        self.minimize_solver = self.scenario_solver_factory("QF_LRA")
        self.clause_set.clear()

    def set_debug(self, msg: str):
        self.debug_name = msg

    def run(self, model: Model, goal: Goal, goal_prop_dict: Dict, config: Configuration,
            solver: JobSolver, printer: Printer):
        total_time = 0.0
        total_size = 0
        common_section = config.get_section("common")
        bound = common_section.get_value("bound")
        time_bound = common_section.get_value("time-bound")
        delta = common_section.get_value("threshold")
        parallel = common_section.get_value("parallel")
        core = int(common_section.get_value("parallel-core"))
        solver_batch_size = int(common_section.get_value("solver-batch-size"))
        if solver_batch_size < 1:
            raise IllegalArgumentError("solver-batch-size must be at least 1")
        is_generalized = common_section.get_value("concrete") != "true"
        smt_preprocess = common_section.get_value("smt-preprocess") == "true"
        if self.runner is not None:
            self.runner.kill_all()

        if parallel == "true":
            self.runner = ParallelAlgRunner(core)
        else:
            self.runner = NormalRunner()

        assert self.runner is not None

        self.clear()
        model.boolean_abstract.clear()

        final_result = "Unknown"
        finished_bound = bound

        # depth = int(bound) * 2
        tau_max = float(time_bound)

        is_reach = isinstance(goal, ReachGoal)
        if is_reach:
            model.gen_reach_condition()
        else:
            model.gen_stl_condition()

        if not is_reach:
            raw_stl_formula = substitution(goal.get_formula(), goal_prop_dict)
            neg_formula = reduce_not(Not(raw_stl_formula))
            # Definition 4.2 handles the original bounded temporal operators
            # directly. Rewriting them into additional F/G/U/R subformulas
            # preserves STL semantics, but not the size of a fully-stable
            # partition at a fixed BMC bound.
            stl_formula = relaxing(neg_formula, float(delta))

            sub_formulas = calc_sub_formulas(stl_formula)

            initial_stl_f = chi(1, 1, stl_formula)
        else:
            initial_stl_f = BoolVal("True")
            sub_formulas = set()

        initial_model_f, initial_track_const = model.init_consts()

        self.scenario_solver.add(initial_stl_f)
        self.scenario_solver.add(initial_model_f)
        self.scenario_solver.add(initial_track_const)
        self.minimize_solver.add(
            Not(And([initial_model_f, initial_stl_f, initial_track_const, Bool("unsat@0")])))
        self.minimize_solver.push()
        self.minimize_solver.add(Bool("unsat@0"))

        self.clause_set.update(clause(And([initial_model_f, initial_stl_f, initial_track_const])))

        # stl
        stl_consts = []
        stl_time_consts = []

        # model
        model_consts = []
        model_track_consts = []

        # For STL, the bound covers mode changes and variable points.  For a
        # state reachability goal there are no STL variable points.
        for b in range(0, int(bound) + 1):
            raise_if_interrupted()
            self.runner.reset_progress()
            bound_started = time.monotonic()

            # generate model consts
            model_f_k, track_f_k = model.k_step_consts(b)
            model_f_k_final, track_f_k_final = model.k_step_consts(b, is_final=True)
            model_consts.append(model_f_k)
            model_track_consts.append(track_f_k)

            if not is_reach:
                stl_f_k_children = list()
                stl_f_k_time_children = list()
                final_f_k = None

                # corresponding stl depth
                # b -> 2 * b + 1 and 2 * b + 2
                for d in range(2 * b + 1, 2 * b + 3):
                    # print("bound: {}, depth: [ {} ]".format(b, d))
                    stl_f_d, time_f_d, final_f_d = k_depth_stl_consts(sub_formulas, d, tau_max)

                    stl_f_k_children.append(stl_f_d)
                    stl_f_k_time_children.append(time_f_d)
                    final_f_k = final_f_d

                time_order_const = time_ordering(2 * b + 2, tau_max)

                assert final_f_k is not None
                stl_f_k = And(stl_f_k_children)
                time_f_k = And(stl_f_k_time_children)

                stl_consts.append(stl_f_k)
                stl_time_consts.append(time_f_k)
            else:
                stl_f_k = BoolVal("True")
                time_f_k = BoolVal("True")
                stl_consts.append(BoolVal("True"))
                stl_time_consts.append(BoolVal("True"))
                time_order_const = reach_time_ordering(2 * b + 2, tau_max)
                final_f_k = goal.k_step_consts(b, float(time_bound), delta, model, goal_prop_dict)
            finished_bound = b
            total_size = acc_size(model_consts)
            total_size += acc_size(stl_consts)
            total_size += acc_size(stl_time_consts)
            total_size += acc_size(model_track_consts)
            total_size += size_of_tree(stl_f_k)
            total_size += size_of_tree(time_f_k)
            total_size += size_of_tree(time_order_const)
            total_size += size_of_tree(final_f_k)

            path_candidates = self.path_provider.candidates(model, b)
            bound_scenarios = 0
            for path_offset, path_candidate in enumerate(path_candidates):
                is_last_path = path_offset == len(path_candidates) - 1
                result, result_model, scenario_time = self.scenario_check(
                    model, b, tau_max, sub_formulas,
                    model_consts, stl_consts, stl_time_consts,
                    model_f_k_final, final_f_k, time_order_const,
                    solver, printer, solver_batch_size,
                    explicit_path=path_candidate.constraint,
                    finalize_bound=is_last_path,
                    is_generalized=is_generalized,
                    smt_preprocess=smt_preprocess,
                )
                total_time += scenario_time
                bound_scenarios += self.last_scenario_count
                if result:
                    printer.bound_finished(
                        b, "sat", time.monotonic() - bound_started,
                        scenarios=bound_scenarios,
                        constraint_size=total_size,
                        found_scenario=self.runner.winning_scenario,
                        witness_label="witness" if is_reach else "counterexample",
                    )
                    if is_reach:
                        return "True", total_time, finished_bound, result_model.get_assignments()
                    return "False", total_time, finished_bound, result_model.get_assignments()

                runner_result, runner_model = self.runner.wait_and_check_sat(
                    lambda completed: printer.scenario_progress(
                        b, **self.runner.progress_snapshot()
                    )
                )
                if runner_result:
                    printer.bound_finished(
                        b, "sat", time.monotonic() - bound_started,
                        scenarios=bound_scenarios,
                        constraint_size=total_size,
                        found_scenario=self.runner.winning_scenario,
                        witness_label="witness" if is_reach else "counterexample",
                    )
                    if is_reach:
                        return "True", self.runner.time, finished_bound, runner_model.get_assignments()
                    return "False", self.runner.time, finished_bound, runner_model.get_assignments()
            printer.bound_finished(
                b, "unknown" if self.runner.had_unknown else "unsat",
                time.monotonic() - bound_started,
                scenarios=bound_scenarios,
                constraint_size=total_size,
            )
            if len(path_candidates) == 0:
                # An explicit transition tree cannot regain paths at a larger
                # exact jump bound after its frontier becomes empty.
                break
        if self.runner.had_unknown:
            return "Unknown", total_time, finished_bound, None
        if is_reach:
            return "False", total_time, finished_bound, None
        return "True", total_time, finished_bound, None

    # accumulated
    def scenario_check(self, model: Model, bound: int, tau_max, sub_formulas: Set[Formula],
                       acc_model: List[Formula], acc_stl: List[Formula], acc_stl_time: List[Formula],
                       model_f_k_final: Formula, stl_final: Formula, stl_time_order: Formula,
                       smt_solver: JobSolver, printer: Printer,
                       solver_batch_size: int,
                       explicit_path: Formula = BoolVal("True"),
                       finalize_bound=True,
                       is_generalized=True,
                       smt_preprocess=False):
        total_time = 0.0

        k_model_f = acc_model[bound]
        k_stl_f = acc_stl[bound]
        k_stl_time_f = acc_stl_time[bound]

        cur_minimize_var = Bool("unsat@{}".format(bound))
        next_minimize_var = Bool("unsat@{}".format(bound + 1))

        current_minimize_info = Eq(cur_minimize_var, And([
            model_f_k_final, k_stl_f, k_stl_time_f, stl_time_order,
            explicit_path, next_minimize_var,
        ]))

        self.minimize_solver.pop()
        self.minimize_solver.push()
        self.minimize_solver.add(current_minimize_info)
        self.minimize_solver.add(next_minimize_var)
        # Temporal rho/Psi_PAR auxiliaries are definitional and therefore do
        # not belong in scenario cubes.  Keep their horizon/base definitions
        # as untracked context while minimizing primary decisions.
        self.minimize_solver.add(stl_final)

        # n_symbolic_path: final, n_symbolic_path_next: non-final
        base_symbolic_path = And([
            model_f_k_final, k_stl_f, k_stl_time_f, stl_time_order,
        ])
        n_symbolic_path = And([base_symbolic_path, explicit_path])
        n_symbolic_path_next = And([k_model_f, k_stl_f, k_stl_time_f])

        self.clause_set.update(clause(n_symbolic_path_next))
        # Explicit path constraints are fixed context, not scenario literals.
        # Keeping them out of the accumulated clause set prevents one path's
        # arithmetic literals from leaking into another path's refinement.
        self.clause_set.update(clause(base_symbolic_path))

        contra_v_const, contra_e_const = contradiction_gen(self.clause_set, sub_formulas)
        contra_v_inv = contradiction_gen_inv(model.boolean_abstract)

        self.scenario_solver.push()
        self.scenario_solver.add(n_symbolic_path)
        self.scenario_solver.add(stl_final)
        self.scenario_solver.add(contra_v_const)
        self.scenario_solver.add(contra_e_const)
        self.scenario_solver.add(contra_v_inv)
        true = BoolVal("True")
        false = BoolVal("False")
        concrete_partition_const = And(partition_obligations(
            sub_formulas, 2 * (bound + 1)
        ))
        counter = 0
        submitted = 0
        pending_candidates: List[Tuple[Formula, Formula]] = []
        pending_scenarios: List[int] = []
        def submit_pending_batch():
            nonlocal submitted
            if len(pending_candidates) == 0:
                return False, None

            first_scenario = pending_scenarios[0]
            last_scenario = pending_scenarios[-1]
            scenario_label = (
                first_scenario if first_scenario == last_scenario
                else "{}-{}".format(first_scenario, last_scenario)
            )
            self.runner.set_debug(
                "{}_b{:03d}_s{}".format(self.debug_name, bound, scenario_label)
            )
            # Multinary formulas retain the supplied list, so detach it before
            # clearing the pending batch.
            batch_candidates = list(pending_candidates)
            # Psi_PAR is required for a returned counterexample, but its
            # definitional variables need not participate in Boolean scenario
            # enumeration.  Validate it once at the concrete boundary.
            batch_formula = And([
                candidate_batch_formula(batch_candidates),
                concrete_partition_const,
            ])
            batch_scenario_count = len(pending_candidates)
            self.runner.set_scenario(scenario_label, batch_scenario_count)
            pending_candidates.clear()
            pending_scenarios.clear()

            self.runner.run(smt_solver, batch_formula)
            submitted += batch_scenario_count
            runner_result, runner_model = self.runner.check_sat()
            printer.scenario_progress(bound, **self.runner.progress_snapshot())
            return runner_result, runner_model

        while True:
            raise_if_interrupted()
            scenario_s = time.monotonic()
            result = self.scenario_solver.check()
            raise_if_interrupted()
            scenario_e = time.monotonic()
            total_time += scenario_e - scenario_s
            # sat, find counterexample
            if result == SolverStatus.SAT:
                m = self.scenario_solver.model()
                assn = m
                assn_dict = assn.get_assignments()
                # pop final and time ordering constraints
                if is_generalized:
                    self.minimize_solver.push()

                    real_set = set()
                    neg_dict: Dict[str, Eq] = dict()
                    bool_assignment_dict: Dict[str, Eq] = dict()
                    for v in assn_dict:
                        valuation = assn_dict[v]
                        if isinstance(v, Bool) and isinstance(valuation, BoolVal):
                            if is_temporal_definitional(v):
                                self.minimize_solver.add(Eq(v, valuation))
                                continue
                            track_id = "p@{}".format(v.id)
                            bool_assignment_dict[track_id] = assert_and_track_assignment(
                                self.minimize_solver, v, valuation, track_id
                            )
                            if valuation == true:
                                neg_dict[track_id] = Eq(v, false)
                            else:
                                neg_dict[track_id] = Eq(v, true)
                        else:
                            assert isinstance(v, Real) or isinstance(v, Int)
                            real_set.add(v)

                    real_dict = dict()
                    for literal in evaluated_arithmetic_literals(
                            self.clause_set, real_set, m):
                        track_id = "p@real_{}".format(id(literal.left))
                        real_dict[track_id] = literal
                        self.minimize_solver.track(literal, track_id)

                    minimize_s = time.monotonic()
                    minimize_result = self.minimize_solver.check()
                    raise_if_interrupted()
                    minimize_e = time.monotonic()
                    total_time += minimize_e - minimize_s

                    if minimize_result != SolverStatus.UNSAT:
                        self.minimize_solver.pop()
                        raise NotSupportedError(
                            "cannot construct an unsatisfiable scenario core"
                        )

                    unsat_cores = self.minimize_solver.unsat_core()

                    # remove tracking infos
                    picked_unsat_cores = set(unsat_cores)
                    self.minimize_solver.pop()
                    p_reals = picked_unsat_cores.difference(set(neg_dict.keys()))
                    core_bool_tracks = picked_unsat_cores.difference(p_reals)

                    # Preserve both polarities selected by the minimized core.
                    # Keeping only positive Boolean choices can make path_const
                    # broader than the scenario that was checked by dReal.
                    path_bool_consts = {
                        bool_assignment_dict[track_id] for track_id in core_bool_tracks
                    }
                    true_core_tracks = {
                        track_id for track_id in core_bool_tracks
                        if bool_assignment_dict[track_id].right == true
                    }
                    # Only true proposition/time variables describe the derived
                    # continuous path constraints passed to dReal.
                    p_bools = pick_time_and_props(true_core_tracks, sub_formulas)
                    path_real_consts = list(map(lambda p: real_dict[p],
                                                filter(lambda p: p in real_dict, [p_real for p_real in p_reals])))

                    path_const_children = list()
                    path_const_children.extend(path_bool_consts)
                    path_const_children.extend(path_real_consts)

                    path_const = And(path_const_children)

                    extra_prop_path, extra_time_path = assn2path(p_bools, sub_formulas, tau_max)
                    # p_chi = (or currentMode = ... (forall ...) ...)
                    extra_prop_path_const = path2const(extra_prop_path, model)
                    extra_time_path_const = time_path2const(extra_time_path)

                    if smt_preprocess:
                        model_abstract_const = relevant_boolean_abstract_links(
                            model.boolean_abstract,
                            And([
                                path_const, stl_final,
                                extra_prop_path_const, extra_time_path_const,
                                explicit_path,
                            ]),
                            boolean_core_assignments(path_const),
                        )
                    else:
                        model_abstract_const = And([
                            Eq(v, model.boolean_abstract[v])
                            for v in model.boolean_abstract
                        ])

                    # to avoid omitting range consts due to unsat core
                    range_consts = list(map(lambda t: t[0], [model.make_range_consts(d) for d in range(0, bound + 1)]))
                    range_const = And(range_consts)

                    # Split scenario-specific and shared constraints so an OR
                    # batch does not duplicate the full flow/invariant model.
                    if model.is_gen_reach_condition() and not smt_preprocess:
                        reduction_dict = dict()
                        for mac in model_abstract_const.children:
                            assert isinstance(mac, Eq)
                            reduction_dict[mac.left] = mac.right
                        scenario_part = substitution(
                            And([path_const, extra_prop_path_const, extra_time_path_const]),
                            reduction_dict,
                        )
                        common_part = substitution(
                            And([stl_final, range_const, explicit_path]), reduction_dict
                        )
                    else:
                        scenario_part = And(
                            [path_const, extra_prop_path_const, extra_time_path_const]
                        )
                        common_part = And(
                            [stl_final, range_const, model_abstract_const, explicit_path]
                        )

                    pending_candidates.append((common_part, scenario_part))
                    pending_scenarios.append(counter)
                    self.runner.record_scenario_generated()
                    printer.scenario_progress(bound, **self.runner.progress_snapshot())
                    runner_result, runner_model = (False, None)
                    if len(pending_candidates) >= solver_batch_size:
                        runner_result, runner_model = submit_pending_batch()
                    if runner_result:
                        self.last_scenario_count = submitted
                        return True, runner_model, self.runner.time

                    generalized_symbolic_path = Not(path_const)
                    self.scenario_solver.add(generalized_symbolic_path)
                    counter += 1

                else:
                    # Keep the complete discrete assignment. Real-valued model
                    # points are deliberately excluded: blocking a single real
                    # point would not make progress over a continuous domain.
                    # Preserve the truth values of arithmetic clauses instead,
                    # so the refinement describes the same symbolic region.
                    concrete_literals = []
                    true_bool_ids = set()
                    real_set = set()
                    for variable, valuation in assn_dict.items():
                        if isinstance(variable, Bool) and isinstance(valuation, BoolVal):
                            if is_temporal_definitional(variable):
                                continue
                            concrete_literals.append(Eq(variable, valuation))
                            if valuation == true:
                                true_bool_ids.add("p@{}".format(variable.id))
                        else:
                            assert isinstance(variable, Real) or isinstance(variable, Int)
                            real_set.add(variable)

                    concrete_literals.extend(evaluated_arithmetic_literals(
                        self.clause_set, real_set, m
                    ))

                    if len(concrete_literals) == 0:
                        raise NotSupportedError("cannot construct a concrete scenario without Boolean choices")

                    concrete_path = And(concrete_literals)
                    p_bools = pick_time_and_props(true_bool_ids, sub_formulas)
                    extra_prop_path, extra_time_path = assn2path(p_bools, sub_formulas, tau_max)
                    extra_prop_path_const = path2const(extra_prop_path, model)
                    extra_time_path_const = time_path2const(extra_time_path)
                    if smt_preprocess:
                        model_abstract_const = relevant_boolean_abstract_links(
                            model.boolean_abstract,
                            And([
                                concrete_path, stl_final,
                                extra_prop_path_const, extra_time_path_const,
                                explicit_path,
                            ]),
                            boolean_core_assignments(concrete_path),
                        )
                    else:
                        model_abstract_const = And(
                            [Eq(v, model.boolean_abstract[v])
                             for v in model.boolean_abstract]
                        )
                    range_const = And(
                        [model.make_range_consts(depth)[0] for depth in range(0, bound + 1)]
                    )

                    if model.is_gen_reach_condition() and not smt_preprocess:
                        reduction_dict = {
                            mac.left: mac.right for mac in model_abstract_const.children
                            if isinstance(mac, Eq)
                        }
                        scenario_part = substitution(
                            And([concrete_path, extra_prop_path_const, extra_time_path_const]),
                            reduction_dict,
                        )
                        common_part = substitution(
                            And([stl_final, range_const, explicit_path]), reduction_dict
                        )
                    else:
                        scenario_part = And(
                            [concrete_path, extra_prop_path_const, extra_time_path_const]
                        )
                        common_part = And(
                            [stl_final, range_const, model_abstract_const, explicit_path]
                        )

                    pending_candidates.append((common_part, scenario_part))
                    pending_scenarios.append(counter)
                    self.runner.record_scenario_generated()
                    printer.scenario_progress(bound, **self.runner.progress_snapshot())
                    runner_result, runner_model = (False, None)
                    if len(pending_candidates) >= solver_batch_size:
                        runner_result, runner_model = submit_pending_batch()
                    if runner_result:
                        self.last_scenario_count = submitted
                        return True, runner_model, self.runner.time

                    # Exclude exactly this Boolean/discrete cube.
                    self.scenario_solver.add(Not(concrete_path))
                    counter += 1
            if result == SolverStatus.UNSAT:
                break

        runner_result, runner_model = submit_pending_batch()
        if runner_result:
            self.last_scenario_count = submitted
            return True, runner_model, self.runner.time

        self.scenario_solver.pop()
        self.minimize_solver.pop()
        if finalize_bound:
            self.scenario_solver.add(n_symbolic_path_next)
            self.minimize_solver.add(Eq(cur_minimize_var, And([
                k_model_f, k_stl_f, k_stl_time_f, next_minimize_var,
            ])))
            self.minimize_solver.push()
            self.minimize_solver.add(next_minimize_var)
        else:
            # Restore the assumption present before checking this path so the
            # next explicit path at the same bound starts from identical state.
            self.minimize_solver.push()
            self.minimize_solver.add(cur_minimize_var)

        self.last_scenario_count = submitted
        return False, None, self.runner.time


def k_depth_stl_consts(sub_formulas: Set[Formula], depth: int, tau_max: float) -> Tuple[Formula, Formula, Formula]:
    goal_consts = set()
    for f in sub_formulas:
        is_globally = isinstance(f, GloballyFormula)
        is_finally = isinstance(f, FinallyFormula)
        if is_proposition(f):
            continue

        is_until = isinstance(f, UntilFormula)
        is_release = isinstance(f, ReleaseFormula)
        if is_finally or is_globally or is_until or is_release:
            goal_consts.update({symbolic_goal(f, i, depth, tau_max) for i in range(1, depth + 1)})

        else:
            goal_consts.add(symbolic_goal(f, depth, depth, tau_max))

    goal_const = And(list(goal_consts))
    # The fixed-start rho recurrence uses the symbolic interval endpoints
    # directly; the legacy T_l/T_r aliases are neither referenced nor needed.
    time_const = BoolVal("True")
    final_const = And([final(f, depth) for f in sub_formulas])

    return goal_const, time_const, final_const


def k_size_stl_formula(model: Model, goal: Goal, goal_prop_dict, bound: int,
                       delta: float, tau_max):
    """Build the complete bounded STL formula used by one-step solving."""
    raw_stl_formula = substitution(goal.get_formula(), goal_prop_dict)
    neg_formula = reduce_not(Not(raw_stl_formula))
    # Keep the original temporal subformula set. A semantics-preserving STL
    # rewrite need not preserve fully-stable partition size at the same bound.
    stl_formula = relaxing(neg_formula, delta)

    return k_size_stl_formula_from_threshold(
        model, stl_formula, bound, tau_max
    )


def k_size_stl_formula_from_threshold(
        model: Model, stl_formula: Formula, bound: int, tau_max):
    """Build one bounded Boolean encoding for an already shifted STL formula."""

    sub_formulas = calc_sub_formulas(stl_formula)
    initial_stl_f = chi(1, 1, stl_formula)
    total_stl_children = [initial_stl_f]
    total_time_children = []
    final_f_k = None

    max_depth = 2 * (bound + 1)
    for depth in range(1, max_depth + 1):
        stl_f_d, time_f_d, final_f_d = k_depth_stl_consts(
            sub_formulas, depth, tau_max
        )
        total_stl_children.append(stl_f_d)
        total_time_children.append(time_f_d)
        final_f_k = final_f_d

    assert final_f_k is not None
    time_order_const = time_ordering(max_depth, tau_max)
    path_const_children = (
        total_stl_children + total_time_children + [time_order_const]
    )
    path_const = And(path_const_children)

    bools = get_bools(path_const)
    p_bools = {boolean.id for boolean in bools}
    extra_prop_path, _ = assn2path(p_bools, sub_formulas, tau_max)
    extra_prop_path_const = path2const(extra_prop_path, model)

    partition_const = And(partition_obligations(sub_formulas, max_depth))
    return And(path_const_children + [
        final_f_k, partition_const, extra_prop_path_const,
    ])


@singledispatch
def get_bools(formula: Formula) -> Set[Bool]:
    return set()


@get_bools.register(Bool)
def _(formula: Bool) -> Set[Bool]:
    return {formula}


@get_bools.register(UnaryFormula)
def _(const: UnaryFormula):
    return get_bools(const.child) if isinstance(const, NonLeaf) else set()


@get_bools.register(BinaryFormula)
def _(const: BinaryFormula):
    if isinstance(const, NonLeaf) or isinstance(const, Eq):
        return get_bools(const.left).union(get_bools(const.right))
    return set()


@get_bools.register(MultinaryFormula)
def _(const: MultinaryFormula):
    result = set()
    if isinstance(const, NonLeaf):
        for child in const.children:
            result.update(get_bools(child))
    return result


def calc_sub_formulas(formula: Formula) -> Set[Formula]:
    return sub_formula(formula)


def is_left_time(sub_formulas: Set[Formula]):
    for f in sub_formulas:
        if isinstance(f, UntilFormula) or isinstance(f, FinallyFormula):
            return True
    return False


def is_right_time(sub_formulas: Set[Formula]):
    for f in sub_formulas:
        if isinstance(f, ReleaseFormula) or isinstance(f, GloballyFormula):
            return True
    return False


def chi(i: int, k: int, f: Formula):
    return Bool("chi^{{{},{}}}_{}".format(i, k, hash(f)))


def t1(i: int, k: int, f: Formula):
    return Bool("T1^{{{},{}}}_{}".format(i, k, hash(f)))


def t2(i: int, k: int, f: Formula):
    return Bool("T2^{{{},{}}}_{}".format(i, k, hash(f)))


def t3(i: int, k: int, f: Formula):
    return Bool("T3^{{{},{}}}_{}".format(i, k, hash(f)))


def rho(i: int, n: int, f: Formula):
    """Paper Definition 4.2 recurrence, with fixed evaluation index ``i``."""
    return Bool("rho^{{{},{}}}_{}".format(i, n, hash(f)))


def par_until(n: int, m: int, f: Formula):
    return Bool("parU^{{{},{}}}_{}".format(n, m, hash(f)))


def par_endpoint(kind: str, n: int, m: int, f: Formula):
    return Bool("parEnd{}^{{{},{}}}_{}".format(kind, n, m, hash(f)))


# sup(J_i)
def symbolic_sup(index: int) -> Real:
    # odd : [ \tau_{(i - 1) / 2}, \tau_{(i - 1) / 2} ]
    # even : ( \tau_{i / 2 - 1}, \tau_{i / 2} )
    tau_index = index / 2
    if index % 2 == 1:
        tau_index = (index - 1) / 2
    return Real("tau_{}".format(int(tau_index)))


# inf(J_i)
def symbolic_inf(index: int) -> Real:
    # odd : [ \tau_{(i - 1) / 2}, \tau_{(i - 1) / 2} ]
    # even : ( \tau_{i / 2 - 1}, \tau_{i / 2} )
    tau_index = index / 2 - 1
    if index % 2 == 1:
        tau_index = (index - 1) / 2
    return Real("tau_{}".format(int(tau_index)))


# final const
def final(f: Formula, depth: int):
    consts = []
    terminal = None
    if isinstance(f, (UntilFormula, FinallyFormula)):
        terminal = BoolVal("False")
    elif isinstance(f, (ReleaseFormula, GloballyFormula)):
        terminal = BoolVal("True")
    if terminal is not None:
        consts.extend(
            Eq(rho(i, depth + 1, f), terminal)
            for i in range(1, depth + 1)
        )
    return And(consts)


def _symbolic_interval(index: int) -> Interval:
    point = index % 2 == 1
    return Interval(point, symbolic_inf(index), point, symbolic_sup(index))


def temporal_candidate(start: int, scan: int, interval: Interval):
    """Encode midpoint(J_start) in J_scan - interval."""
    start_j = _symbolic_interval(start)
    scan_j = _symbolic_interval(scan)
    midpoint = Div(Add(start_j.left, start_j.right), RealVal("2.0"))
    conditions = []
    if "inf" not in str(interval.right):
        lower = Sub(scan_j.left, interval.right)
        conditions.append(
            midpoint >= lower
            if scan_j.left_end and interval.right_end else midpoint > lower
        )
    upper = Sub(scan_j.right, interval.left)
    conditions.append(
        midpoint <= upper
        if scan_j.right_end and interval.left_end else midpoint < upper
    )
    return And(conditions)


def _temporal_operands(f: Formula, index: int):
    if isinstance(f, UntilFormula):
        return chi(index, index, f.left), chi(index, index, f.right)
    if isinstance(f, ReleaseFormula):
        return Not(chi(index, index, f.left)), Not(chi(index, index, f.right))
    if isinstance(f, FinallyFormula):
        return BoolVal("True"), chi(index, index, f.child)
    if isinstance(f, GloballyFormula):
        return BoolVal("True"), Not(chi(index, index, f.child))
    raise NotSupportedError("not a temporal formula")


def _edge(value, previous=None, following=None):
    rising = value if previous is None else And([value, Not(previous)])
    falling = value if following is None else And([value, Not(following)])
    return rising, falling


def _endpoint_membership(value, index: int):
    return Or([
        Eq(value, symbolic_inf(index)), Eq(value, symbolic_sup(index))
    ])


def temporal_partition_obligations(f: Formula, depth: int):
    """Definition 4.3 fully-stable partition conjuncts."""
    interval = f.local_time
    for m in range(1, depth + 1):
        left_m, right_m = _temporal_operands(f, m)
        left_prev, right_prev = (
            _temporal_operands(f, m - 1) if m > 1 else (None, None)
        )
        left_next, right_next = (
            _temporal_operands(f, m + 1) if m < depth else (None, None)
        )
        left_rise, left_fall = _edge(left_m, left_prev, left_next)
        right_rise, right_fall = _edge(right_m, right_prev, right_next)

        for n in range(m, 0, -1):
            chain = And([left_m, right_m]) if n == m else And([
                _temporal_operands(f, n)[0], par_until(n + 1, m, f)
            ])
            yield Eq(par_until(n, m, f), chain)

        candidates = [("F",
            Sub(symbolic_sup(m), interval.left),
            Or([left_fall, right_fall]),
        )]
        if "inf" not in str(interval.right):
            candidates.append(("R",
                Sub(symbolic_inf(m), interval.right),
                Or([left_rise, right_rise]),
            ))

        for kind, value, edge_condition in candidates:
            cand_parts = []
            for n in range(m, 0, -1):
                endpoint_here = _endpoint_membership(value, n)
                endpoint_suffix = (
                    endpoint_here if n == m else Or([
                        endpoint_here, par_endpoint(kind, n + 1, m, f)
                    ])
                )
                yield Eq(par_endpoint(kind, n, m, f), endpoint_suffix)
                cand_parts.append(Implies(
                    And([par_until(n, m, f), symbolic_inf(n) <= value]),
                    par_endpoint(kind, n, m, f),
                ))
            yield Implies(edge_condition, And(cand_parts))


def partition_obligations(sub_formulas: Set[Formula], depth: int):
    obligations = []
    for f in sub_formulas:
        if isinstance(f, (
                UntilFormula, ReleaseFormula,
                FinallyFormula, GloballyFormula)):
            obligations.extend(temporal_partition_obligations(f, depth))
    return obligations


def symbolic_goal(f: Formula, i: int, d: int, tau_max):
    # if isinstance(f, Bool):
    #     assert i == d
    #     return None

    if isinstance(f, And):
        assert i == d
        # assert len(f.children) == 2
        left = chi(i, d, f)
        right = And([chi(i, i, child) for child in f.children])
        return Eq(left, right)

    if isinstance(f, Or):
        assert i == d
        # assert len(f.children) == 2
        left = chi(i, d, f)
        right = Or([chi(i, i, child) for child in f.children])
        return Eq(left, right)

    if isinstance(f, UntilFormula):
        step = Or([
            And([temporal_candidate(i, d, f.local_time),
                 chi(d, d, f.left), chi(d, d, f.right)]),
            And([chi(d, d, f.left), rho(i, d + 1, f)]),
        ])
        return And([
            Eq(rho(i, d, f), step),
            Eq(chi(i, i, f), rho(i, i, f))
            if i == d else BoolVal("True"),
        ])

    if isinstance(f, ReleaseFormula):
        candidate = temporal_candidate(i, d, f.local_time)
        step = And([
            Or([Not(candidate), chi(d, d, f.left), chi(d, d, f.right)]),
            Or([chi(d, d, f.left), rho(i, d + 1, f)]),
        ])
        return And([
            Eq(rho(i, d, f), step),
            Eq(chi(i, i, f), rho(i, i, f))
            if i == d else BoolVal("True"),
        ])

    if isinstance(f, GloballyFormula):
        candidate = temporal_candidate(i, d, f.local_time)
        step = And([
            Or([Not(candidate), chi(d, d, f.child)]), rho(i, d + 1, f)
        ])
        return And([
            Eq(rho(i, d, f), step),
            Eq(chi(i, i, f), rho(i, i, f))
            if i == d else BoolVal("True"),
        ])

    if isinstance(f, FinallyFormula):
        step = Or([
            And([temporal_candidate(i, d, f.local_time),
                 chi(d, d, f.child)]), rho(i, d + 1, f)
        ])
        return And([
            Eq(rho(i, d, f), step),
            Eq(chi(i, i, f), rho(i, i, f))
            if i == d else BoolVal("True"),
        ])

    raise NotSupportedError("cannot find related rule")


def globally_time_const(depth: int, f: Formula) -> Set[Formula]:
    assert isinstance(f, GloballyFormula)

    consts = set()

    sup_k = symbolic_sup(depth)
    inf_k = symbolic_inf(depth)

    sup_formula = f.local_time.right
    inf_formula = f.local_time.left
    J = f.local_time

    # 1 ... depth
    for i in range(1, depth + 1):
        sup_i = symbolic_sup(i)
        inf_i = symbolic_inf(i)

        t_1 = t1(i, depth, f)
        t_2 = t2(i, depth, f)

        add_left_close = True if depth % 2 == 1 and J.left_end else False
        add_right_close = True if depth % 2 == 1 and J.right_end else False

        left_jk_locate = Lt(sup_k, Add(inf_i, inf_formula)) if depth % 2 == 1 and add_left_close else Leq(sup_k,
                                                                                                          Add(inf_i,
                                                                                                              inf_formula))
        right_jk_locate = Gt(inf_k, Add(sup_i, sup_formula)) if depth % 2 == 1 and add_right_close else Geq(inf_k,
                                                                                                            Add(sup_i,
                                                                                                                sup_formula))

        const1 = Eq(t_1, left_jk_locate)
        const2 = Eq(t_2, right_jk_locate)

        consts.add(const1)
        consts.add(const2)
    return consts


def finally_time_const(depth: int, f: Formula) -> Set[Formula]:
    assert isinstance(f, FinallyFormula)

    consts = set()
    inf_k = symbolic_inf(depth)
    # 1 ... depth

    kl_interval = True if depth % 2 == 1 and f.local_time.right_end else False

    for i in range(1, depth + 1):
        inf_i = symbolic_inf(i)

        sup_formula = f.local_time.right
        t_3 = t3(i, depth, f)

        time_cond = Lt(Sub(inf_k, sup_formula), inf_i) if (not kl_interval) and i % 2 == 1 else Leq(
            Sub(inf_k, sup_formula), inf_i)

        const = Eq(t_3, time_cond)
        consts.add(const)
    return consts


def time_ordering(n: int, tau_max: float) -> And:
    # n: even
    # Paper trajectory encoding:
    # 0 = \tau_0 <= ... <= \tau_{n/2-1} < \tau_{n/2} = \tau_max.
    time_order: Set[Constraint] = set()
    time_order.add(Eq(RealVal("0"), Real("tau_0")))
    time_order.add(Eq(symbolic_sup(n), RealVal(str(tau_max))))

    for i in range(1, n, 2):
        current = symbolic_sup(i)
        following = symbolic_sup(i + 1)
        time_order.add(
            current < following if i == n - 1 else current <= following
        )

    return And(list(time_order))


def reach_time_ordering(n: int, tau_max: float) -> And:
    # n: even
    # 0 = \tau_0 < \tau_1 < ... < \tau_{i / 2} <= \tau_max
    time_order: Set[Constraint] = set()
    time_order.add(Eq(RealVal("0"), Real("tau_0")))
    time_order.add(Leq(symbolic_sup(n), RealVal(str(tau_max))))

    for i in range(1, n, 2):
        time_order.add(symbolic_sup(i) < symbolic_sup(i + 1))

    return And(list(time_order))


def sub_formula(formula: Formula) -> Set[Formula]:
    assert isinstance(formula, Formula)
    set_of_formulas = set()
    count = 0

    # first children
    root = (count, formula)

    waiting_queue = set()
    waiting_queue.add(root)
    set_of_formulas.add(formula)

    while len(waiting_queue) > 0:
        count = count + 1
        _, f = waiting_queue.pop()

        if is_proposition(f):
            set_of_formulas.add(f)
        elif isinstance(f, UnaryFormula):
            set_of_formulas.add(f)
            waiting_queue.add((count, f.child))
        elif isinstance(f, BinaryFormula):
            set_of_formulas.add(f)
            waiting_queue.add((count, f.left))
            waiting_queue.add((count, f.right))
        elif isinstance(f, MultinaryFormula):
            set_of_formulas.add(f)
            for child in f.children:
                waiting_queue.add((count, child))
        else:
            continue
    return set_of_formulas


def is_proposition(formula: Formula):
    if isinstance(formula, Bool):
        return True
    else:
        if not isinstance(formula, Variable) and isinstance(formula, Leaf):
            return True
    return False


def bound_dict(picked_bools: List[Bool], sub_formulas: Set[Formula], model_boolean_abst: Dict) -> Tuple[
    Set[Bool], Dict[int, Set[Formula]], Dict[int, Set[Formula]]
]:
    path_const_children = set()
    # key: depth
    prop_dict: Dict[int, Set[Formula]] = dict()
    # key: bound
    inv_dict: Dict[int, Set[Formula]] = dict()

    time_type1_prefix = ["T1", "T2", "T3"]
    time_type2_prefix = "T"
    integral_prefix = "newIntegral"
    invariant_prefix = "invAtomicID"

    for picked_bool in picked_bools:
        is_chi = "chi" in picked_bool.id
        # check if v_info is applied to unsat_core id
        # unsat_core contains at least one of prefix in v_prefixes
        is_time_type1 = reduce(lambda b, acc: acc or b, [prefix in picked_bool.id for prefix in time_type1_prefix],
                               False)
        if is_chi or is_time_type1:
            formula, f_i, f_k = v_type1_info(picked_bool.id, sub_formulas)
            is_formula_prop = is_proposition(formula)

            # if path has an index f_k
            if is_formula_prop:
                if is_time_type1:
                    path_const_children.add(picked_bool)
                else:
                    if f_k in prop_dict:
                        prop_dict[f_k].add(formula)
                    else:
                        prop_dict[f_k] = {formula}

        is_time_type2 = time_type2_prefix in picked_bool.id and not is_time_type1
        if is_time_type2:
            # if path has an index f_k
            path_const_children.add(picked_bool)

        is_integral = integral_prefix in picked_bool.id
        if is_integral:
            path_const_children.add(picked_bool)

        is_invariant = invariant_prefix in picked_bool.id
        if is_invariant:
            assert picked_bool in model_boolean_abst
            invariant = model_boolean_abst[picked_bool]

            assert isinstance(invariant, Forall)
            module_index, bound = inv_index_info(picked_bool.id)
            if bound in inv_dict:
                inv_dict[bound].add(invariant.const)
            else:
                inv_dict[bound] = {invariant.const}

    # inv_dict key is bound
    # time_dict key is depth
    return path_const_children, prop_dict, inv_dict


def extra_path_dict(prop_dict: Dict[int, Set[Formula]],
                    inv_dict: Dict[int, Set[Formula]]) -> Dict[int, Set[Formula]]:
    # key: depth
    path_dict: Dict[int, Set[Formula]] = dict()
    for depth in prop_dict:
        bound = depth2bound(depth)
        prop_consts = prop_dict[depth]
        is_vertex = depth % 2 == 0

        renamed_consts = set(map(lambda f: rename(f, bound, is_vertex)[0], prop_consts))
        if bound in path_dict:
            path_dict[bound].update(renamed_consts)
        else:
            path_dict[bound] = renamed_consts

    for bound in inv_dict:
        depth = 2 * (bound + 1)
        if depth in path_dict:
            path_dict[depth].update(inv_dict[bound])
        else:
            path_dict[depth] = inv_dict[bound]

    return path_dict


def extra_path_formula(path_dict: Dict[int, Set[Formula]], module_index_dict: Dict[int, int], model: Model):
    path_const_children = list()
    # depth / 2 = bound
    for depth in path_dict:
        path_formula_at_depth = And(list(path_dict[depth]))
        bound = depth2bound(depth)
        is_vertex = depth % 2 == 0
        if is_vertex:
            module_index = module_index_dict[bound]
            assert module_index < len(model.modules)
            integral = model.boolean_abstract[Bool("newIntegral_{}_{}".format(module_index, bound))]
            # renamed_integral = rename_integral(integral, bound, is_vertex)
            forall = Forall(module_index, symbolic_sup(depth), symbolic_inf(depth),
                            path_formula_at_depth, integral)
            path_const_children.append(forall)
        else:
            path_const_children.append(path_formula_at_depth)
    return And(path_const_children)


def pick_current_module_dict(real_clause_set: Set[Formula]) -> Dict[int, int]:
    cur_mode_prefix = "currentMode_"
    cur_module_dict: Dict[int, int] = dict()
    for real_clause in real_clause_set:
        if isinstance(real_clause, Eq):
            if isinstance(real_clause.left, Real) and isinstance(real_clause.right, RealVal):
                real_id = real_clause.left.id
                if cur_mode_prefix in real_id:
                    bound = int(real_id.split("_")[1])
                    module_index = int(real_clause.right.value)

                    assert bound not in cur_module_dict
                    cur_module_dict[bound] = module_index
    return cur_module_dict


def pick_time_and_props(unsat_cores: Set[str], sub_formulas: Set[Formula]) -> Set[str]:
    picked_set: Set[str] = set()

    time_type1_prefix = ["T1", "T2", "T3"]
    time_type2_prefix = "T"
    model_type = ["invAtomicID", "newIntegral"]

    for unsat_core in unsat_cores:
        is_chi = "chi" in unsat_core
        # check if v_info is applied to unsat_core id
        # unsat_core contains at least one of prefix in v_prefixes
        is_time_type1 = reduce(lambda b, acc: acc or b, [prefix in unsat_core for prefix in time_type1_prefix], False)
        if is_chi or is_time_type1:
            formula, f_i, f_k = v_type1_info(unsat_core, sub_formulas)
            is_formula_prop = is_proposition(formula)

            # if path has an index f_k
            if is_formula_prop:
                picked_set.add(unsat_core)

        is_time_type2 = time_type2_prefix in unsat_core and not is_time_type1
        if is_time_type2:
            # if path has an index f_k
            picked_set.add(unsat_core)

        is_model_type = reduce(lambda b, acc: acc or b, [prefix in unsat_core for prefix in model_type], False)
        if is_model_type:
            picked_set.add(unsat_core)

    return picked_set


def assn2path(unsat_cores: Set[str], sub_formulas: Set[Formula], tau_max: float) -> Tuple[
    Dict[Tuple[int, Bool], Formula],
    Dict[Tuple[int, Bool], Formula]
]:
    path_dict: Dict[Tuple[int, Bool], Formula] = dict()
    time_dict: Dict[Tuple[int, Bool], Formula] = dict()

    time_type1_prefix = ["T1", "T2", "T3"]
    time_type2_prefix = "T"

    for unsat_core in unsat_cores:
        is_chi = "chi" in unsat_core
        # check if v_info is applied to unsat_core id
        # unsat_core contains at least one of prefix in v_prefixes
        is_time_type1 = reduce(lambda b, acc: acc or b, [prefix in unsat_core for prefix in time_type1_prefix], False)
        if is_chi or is_time_type1:
            formula, f_i, f_k = v_type1_info(unsat_core, sub_formulas)
            is_formula_prop = is_proposition(formula)

            pair = (f_k, Bool(unsat_core))
            assert pair not in path_dict
            # if path has an index f_k
            if is_formula_prop:
                if is_chi:
                    path_dict[pair] = formula
                if is_time_type1:
                    time_dict[pair] = formula

        is_time_type2 = time_type2_prefix in unsat_core and not is_time_type1
        if is_time_type2:
            formula, f_i = v_type2_info(unsat_core, tau_max)
            pair = (f_i, Bool(unsat_core))
            assert is_proposition(formula) and pair not in path_dict

            # if path has an index f_k
            time_dict[pair] = formula

    return path_dict, time_dict


def is_mode_variable(b: Bool, model: Model):
    if b.id in model.mode_var_dict:
        return True
    return False


def path2const(path: Dict[Tuple[int, Bool], Formula], model: Model):
    path_const_children = list()
    # depth / 2 = bound
    for (depth, v) in path:
        bound = int((depth - 1) / 2)
        is_vertex = depth % 2 == 0
        formula = path[(depth, v)]
        renamed_const, rename_dict = rename(formula, bound, is_vertex)
        if is_vertex:
            #  if mode variable, do not add
            if is_mode_variable(v, model):
                renamed_e_const, _ = rename(formula, bound, False)
                path_const_children.append(Eq(Bool(v.id.replace("p@", "")), renamed_e_const))
                continue

            chi_prop_children = list()
            for module_index, module in enumerate(model.modules):
                integrals = module["flow"]
                # renamed_integrals = substitution(integrals, rename_dict)
                forall = Forall(module_index, symbolic_sup(depth), symbolic_inf(depth),
                                renamed_const,
                                model.boolean_abstract[Bool("newIntegral_{}_{}".format(module_index, bound))])
                matching = Eq(Real("currentMode_{}".format(bound)), RealVal(str(module_index)))
                chi_prop_children.append(And([matching, renamed_const, forall]))
            path_const_children.append(Eq(Bool(v.id.replace("p@", "")), Or(chi_prop_children)))
        else:
            renamed_e_const, _ = rename(formula, bound, False)
            path_const_children.append(Eq(Bool(v.id.replace("p@", "")), renamed_e_const))
    return And(path_const_children)


def time_path2const(path: Dict[Tuple[int, Bool], Formula]):
    path_const_children = list()
    # depth / 2 = bound
    for (depth, v) in path:
        bound = int((depth - 1) / 2)
        is_vertex = depth % 2 == 0
        formula = path[(depth, v)]
        renamed_const, _ = rename(formula, bound, is_vertex)

        if is_vertex:
            path_const_children.append(Eq(Bool(v.id.replace("p@", "")), renamed_const))
        else:
            renamed_e_const, _ = rename(formula, bound, False)
            path_const_children.append(Eq(Bool(v.id.replace("p@", "")), renamed_e_const))
    return And(path_const_children)


def v_type_model_info(v_id: str):
    module_id = v_id.split("@")[1]
    bound_str = v_id.split("@")[2]

    assert "m_" in module_id and "const_" in bound_str

    module_index = module_id.split("_")[1]
    bound = bound_str.split("_")[1]
    return int(module_index), int(bound)


def v_type1_info(v_id: str, sub_formulas: Set[Formula]) -> Tuple[Formula, int, int]:
    is_chi = "chi" in v_id
    is_t1 = "T1" in v_id
    is_t2 = "T2" in v_id
    is_t3 = "T3" in v_id

    if is_chi:
        return type1_info(v_id, sub_formulas)

    # T1, T2, T3
    f, f_i, f_k = type1_info(v_id, sub_formulas)

    assert isinstance(f, GloballyFormula) or isinstance(f, FinallyFormula)
    sup_formula = f.local_time.right
    inf_formula = f.local_time.left

    sup_k = symbolic_sup(f_k)
    inf_k = symbolic_inf(f_k)

    sup_i = symbolic_sup(f_i)
    inf_i = symbolic_inf(f_i)

    if is_t1:
        return Leq(sup_k, Add(inf_i, inf_formula)), f_i, f_k

    if is_t2:
        return Leq(Add(sup_i, sup_formula), inf_k), f_i, f_k

    if is_t3:
        return Leq(Sub(inf_k, sup_formula), inf_i), f_i, f_k

    raise NotSupportedError("unknown time type")


def v_type2_info(v_id: str, tau_max: float) -> Tuple[Formula, int]:
    return type2_info(v_id, tau_max)


# type1: v_id^{i, k}_{hash}
def type1_info(v_id: str, sub_formulas: Set[Formula]) -> Tuple[Formula, int, int]:
    hash_id = int(v_id.split("_")[1])
    i, k = type1_index_info(v_id)

    for f in sub_formulas:
        if hash(f) == hash_id:
            return f, i, k

    raise NotSupportedError("cannot find corresponding formula")


# type2: v_id^{i}_{l} or v_id^{i}_{r}
def type2_info(v_id: str, tau_max) -> Tuple[Formula, int]:
    left_or_right = v_id.split("_")[1]
    is_left = left_or_right == "l"
    is_right = left_or_right == "r"

    i = type2_index_info(v_id)

    if is_left:
        return symbolic_sup(i) <= RealVal(str(tau_max)), i

    if is_right:
        return Eq(symbolic_sup(i), RealVal(str(tau_max))), i

    raise NotSupportedError("cannot find corresponding formula")


def type1_index_info(v_id: str) -> Tuple[int, int]:
    # {i, k}
    ik_encoded_str = v_id.split("_")[0].split("^")[1][1:-1]
    ik = ik_encoded_str.split(",")

    assert len(ik) == 2
    i = int(ik[0])
    k = int(ik[1])
    return i, k


def type2_index_info(v_id: str):
    # {i}
    return int(v_id.split("_")[0].split("^")[1])


def inv_index_info(v_id: str):
    # bound
    bound = int(v_id.split("_")[2])
    module_index = int(v_id.split("_")[1][0])
    return module_index, bound


def rename(f: Formula, bound: int, is_vertex=True):
    variables = get_vars(f)
    rename_dict = dict()
    for v in variables:
        if isinstance(v, Bool):
            indexed_v = Bool("{}_{}".format(v.id, bound))
            rename_dict[v] = indexed_v
        if isinstance(v, Real) and "tau_" not in v.id:
            if is_vertex:
                indexed_v = Real("{}_{}_0".format(v.id, bound))
            else:
                if bound > 0:
                    indexed_v = Real("{}_{}_t".format(v.id, bound - 1))
                else:
                    indexed_v = Real("{}_{}_0".format(v.id, bound))
            rename_dict[v] = indexed_v
    return substitution(f, rename_dict), rename_dict


def depth2bound(depth: int):
    return int((depth - 1) / 2)


# vertex, edge
def contradiction_gen(clause_set, sub_formulas):
    const_edge_children = list()
    const_vertex_children = list()
    for c in clause_set:
        if isinstance(c, Bool):
            is_chi = "chi" in c.id
            if is_chi:
                formula, f_i, f_k = v_type1_info(c.id, sub_formulas)
                is_formula_prop = is_proposition(formula)
                is_edge = f_k % 2 == 1
                is_vertex = f_k % 2 == 0

                bound = depth2bound(f_k)

                # if path has an index f_k
                if is_formula_prop and is_edge:
                    renamed_f, _ = rename(formula, bound, is_vertex=False)
                    const_edge_children.append(Eq(c, renamed_f))

                if is_formula_prop and is_vertex:
                    renamed_f_v, _ = rename(formula, bound, is_vertex=True)
                    renamed_f_e, _ = rename(formula, bound + 1, is_vertex=False)
                    const_vertex_children.append(Eq(c, And([renamed_f_v, renamed_f_e])))
    return And(const_vertex_children), And(const_edge_children)


def contradiction_gen_inv(boolean_dict):
    inv_eq = list()
    for b in boolean_dict:
        is_inv = "invAtomicID" in b.id
        if is_inv:
            forall = boolean_dict[b]
            assert isinstance(forall, Forall)
            inv_eq.append(Eq(b, forall.const))
    return And(inv_eq)


def acc_size(acc: List[Formula]):
    return size_of_tree(And(acc))
