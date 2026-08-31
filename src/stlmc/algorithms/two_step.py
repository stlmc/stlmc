import time
from functools import reduce, singledispatch
from typing import *

from ..constraints.operations import *
from ..execution.runner import Algorithm, NormalRunner, ParallelAlgRunner
from ..objects.configuration import Configuration
from ..objects.goal import Goal, ReachGoal
from ..objects.model import Model
from ..solver.abstract_solver import JobSolver, SolverStatus
from ..constraints.operations import size_of_tree
from ..utils.print import Printer
from ..utils.interrupt import raise_if_interrupted
from ..exceptions import IllegalArgumentError
from ..encoding.batching import partitioned_candidate_batch_formula
from ..encoding.fully_stable_partition import FullyStablePartitionEncoding
from ..encoding.fully_stable_stl import (
    calc_sub_formulas, final, is_proposition, k_depth_stl_consts,
    prepare_fully_stable_stl_formula, stl_depth_components, sub_formula,
    symbolic_goal,
)
from ..encoding.path import PathProvider, SymbolicPathProvider
from ..encoding.symbolic_discrete import (
    chi, formula_id, reach_time_ordering, rho, symbolic_inf, symbolic_sup,
    time_ordering,
)
from .scenario_refinement import (
    assert_and_track_assignment, boolean_core_assignments,
    evaluated_arithmetic_literals, is_temporal_definitional,
    relevant_boolean_abstract_links, scenario_enumeration_finished,
)


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
            stl_formula = prepare_fully_stable_stl_formula(
                goal, goal_prop_dict, float(delta)
            )

            sub_formulas = calc_sub_formulas(stl_formula)
            partition_encoding = FullyStablePartitionEncoding(sub_formulas)

            initial_stl_f = chi(1, 1, stl_formula)
        else:
            initial_stl_f = BoolVal("True")
            sub_formulas = set()
            partition_encoding = FullyStablePartitionEncoding(sub_formulas)

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
                # corresponding stl depth
                # b -> 2 * b + 1 and 2 * b + 2
                stl_f_k_children, stl_f_k_time_children, final_f_k = (
                    stl_depth_components(
                        sub_formulas, range(2 * b + 1, 2 * b + 3), tau_max
                    )
                )

                time_order_const = time_ordering(2 * b + 2, tau_max)

                assert final_f_k is not None
                stl_f_k = And(stl_f_k_children)
                time_f_k = And(stl_f_k_time_children)

                stl_consts.append(stl_f_k)
                stl_time_consts.append(time_f_k)
                partition_encoding.extend_to(2 * (b + 1))
                partition_const = partition_encoding.formula()
            else:
                stl_f_k = BoolVal("True")
                time_f_k = BoolVal("True")
                stl_consts.append(BoolVal("True"))
                stl_time_consts.append(BoolVal("True"))
                time_order_const = reach_time_ordering(2 * b + 2, tau_max)
                final_f_k = goal.k_step_consts(b, float(time_bound), delta, model, goal_prop_dict)
                partition_const = BoolVal("True")
            finished_bound = b
            total_size = acc_size(model_consts)
            total_size += acc_size(stl_consts)
            total_size += acc_size(stl_time_consts)
            total_size += acc_size(model_track_consts)
            total_size += size_of_tree(stl_f_k)
            total_size += size_of_tree(time_f_k)
            total_size += size_of_tree(time_order_const)
            total_size += size_of_tree(final_f_k)
            total_size += size_of_tree(partition_const)

            path_candidates = self.path_provider.candidates(model, b)
            bound_scenarios = 0
            for path_offset, path_candidate in enumerate(path_candidates):
                is_last_path = path_offset == len(path_candidates) - 1
                result, result_model, scenario_time = self.scenario_check(
                    model, b, tau_max, sub_formulas,
                    model_consts, stl_consts, stl_time_consts,
                    model_f_k_final, final_f_k, time_order_const,
                    partition_const,
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
                       partition_const: Formula,
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
            partition_const, explicit_path, next_minimize_var,
        ]))

        self.minimize_solver.pop()
        self.minimize_solver.push()
        self.minimize_solver.add(current_minimize_info)
        self.minimize_solver.add(next_minimize_var)
        # Temporal rho/Psi_PAR auxiliaries are definitional and therefore do
        # not belong in scenario cubes.  Keep their horizon/base definitions
        # as untracked context while minimizing primary decisions.
        self.minimize_solver.add(stl_final)
        # Paper Algorithm 2 abstracts only flow and invariant constraints.
        # Psi_PAR is QF_LRA and must constrain scenario generation/minimization,
        # rather than being deferred exclusively to the nonlinear refinement.

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
        self.scenario_solver.add(partition_const)
        self.scenario_solver.add(contra_v_const)
        self.scenario_solver.add(contra_e_const)
        self.scenario_solver.add(contra_v_inv)
        true = BoolVal("True")
        false = BoolVal("False")
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
            # Psi_PAR is part of the final encoding. Factor it once around the
            # candidate disjunction instead of projecting it out after
            # abstraction-side minimization.
            batch_formula = partitioned_candidate_batch_formula(
                batch_candidates, partition_const
            )
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
                                # Definitional values are context for proving
                                # the scenario, but are never scenario literals
                                # or concrete path constraints themselves.
                                literal = Eq(v, valuation)
                                self.minimize_solver.add(literal)
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
                    # Psi_PAR depends on shifted symbolic endpoints. Include
                    # those evaluated arithmetic atoms in the candidate core,
                    # without polluting the persistent model clause set used
                    # for contradiction learning across bounds.
                    minimization_clauses = self.clause_set.union(
                        clause(partition_const)
                    )
                    for literal in evaluated_arithmetic_literals(
                            minimization_clauses, real_set, m):
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
                            [stl_final, range_const, model_abstract_const,
                             explicit_path]
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
                            And([stl_final, partition_const, range_const,
                                 explicit_path]), reduction_dict
                        )
                    else:
                        scenario_part = And(
                            [concrete_path, extra_prop_path_const, extra_time_path_const]
                        )
                        common_part = And(
                            [stl_final, partition_const, range_const,
                             model_abstract_const, explicit_path]
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
            if result == SolverStatus.UNKNOWN:
                # Rechecking an unchanged incremental query cannot make
                # progress and otherwise spins forever.
                self.runner.had_unknown = True
            if scenario_enumeration_finished(result):
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


def k_size_stl_formula(model: Model, goal: Goal, goal_prop_dict, bound: int,
                       delta: float, tau_max):
    """Build the complete bounded STL formula used by one-step solving."""
    stl_formula = prepare_fully_stable_stl_formula(
        goal, goal_prop_dict, delta
    )

    return k_size_stl_formula_from_threshold(
        model, stl_formula, bound, tau_max
    )


def k_size_stl_formula_from_threshold(
        model: Model, stl_formula: Formula, bound: int, tau_max):
    """Build one bounded Boolean encoding for an already shifted STL formula."""

    sub_formulas = calc_sub_formulas(stl_formula)
    initial_stl_f = chi(1, 1, stl_formula)
    total_stl_children = [initial_stl_f]
    max_depth = 2 * (bound + 1)
    depth_stl_children, total_time_children, final_f_k = (
        stl_depth_components(sub_formulas, range(1, max_depth + 1), tau_max)
    )
    total_stl_children.extend(depth_stl_children)
    time_order_const = time_ordering(max_depth, tau_max)
    path_const_children = (
        total_stl_children + total_time_children + [time_order_const]
    )
    path_const = And(path_const_children)

    bools = get_bools(path_const)
    p_bools = {boolean.id for boolean in bools}
    extra_prop_path, _ = assn2path(p_bools, sub_formulas, tau_max)
    extra_prop_path_const = path2const(extra_prop_path, model)

    partition_encoding = FullyStablePartitionEncoding(sub_formulas)
    partition_encoding.extend_to(max_depth)
    partition_const = partition_encoding.formula()
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
    structural_id = v_id.split("_", 1)[1]
    i, k = type1_index_info(v_id)

    for f in sub_formulas:
        if formula_id(f) == structural_id:
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
