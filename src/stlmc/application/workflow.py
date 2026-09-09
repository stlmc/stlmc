"""Application workflow for preparing and executing verification requests."""

import os.path
import time
from dataclasses import dataclass

from ..artifacts.writer import write_verification_artifacts
from ..constraints.substitution import substitution
from ..exceptions import IllegalArgumentError, NotSupportedError, ParsingError
from ..objects.goal import ReachGoal, reach_goal, validate_reach_formula
from ..parser.checker import check_dynamics, check_validity
from ..solver.capability import (
    expression_requires_dreal, model_requires_dreal,
    validate_formula_solver_support, validate_model_solver_support,
)
from ..solver.solver_factory import SolverFactory
from .algorithm_factory import AlgorithmFactory
from .options import RunOptions
from .result import AlgorithmResult, interpret_algorithm_result


@dataclass(frozen=True)
class PreparedRun:
    file_name: str
    configuration: object
    options: RunOptions
    model: object
    proposition_definitions: dict
    goals: tuple
    goal_labels: dict
    solver: object
    algorithm: object


def validate_requested_goal_labels(requested_labels, goal_labels):
    available_labels = sorted(set(goal_labels.values()))
    missing = sorted(set(requested_labels).difference(available_labels))
    if missing:
        available = ", ".join(available_labels) if available_labels else "none"
        raise IllegalArgumentError(
            "unknown goal label(s): {}; available goals: {}".format(
                ", ".join(missing), available
            )
        )


class RunPreparer:
    """Load domain inputs and select infrastructure for one CLI request."""

    def __init__(self, solver_factory=None, object_manager_factory=None):
        self.solver_factory = solver_factory or SolverFactory()
        if object_manager_factory is None:
            from .model_loader import ObjectManager

            object_manager_factory = ObjectManager
        self.object_manager_factory = object_manager_factory

    def prepare(self, file_name, configuration, update_solver_config):
        options = RunOptions.from_configuration(configuration)
        common = configuration.get_section("common")
        common.set_value("time-horizon", str(options.time_horizon))
        common.set_value("parallel-core", str(options.parallel_core))

        manager = self.object_manager_factory()
        model, definitions, goals, labels = manager.generate_objects(file_name)
        validate_requested_goal_labels(options.goal_labels, labels)

        solver_name = options.solver
        if solver_name == "auto":
            solver_name = self._select_solver(model, goals, definitions)
            common.set_value("solver", solver_name)
            if solver_name == "yices":
                logic = "QF_NRA" if check_dynamics(model) == "poly" else "QF_LRA"
                configuration.get_section("yices").set_value("logic", logic)
            options = options.with_solver(solver_name)

        update_solver_config(solver_name)
        check_validity(configuration)
        validate_model_solver_support(solver_name, model)
        solver = self.solver_factory.generate_solver(configuration)
        algorithm = AlgorithmFactory(
            configuration,
            self.solver_factory.generate_formula_solver_factory(),
        ).generate()
        return PreparedRun(
            file_name=file_name,
            configuration=configuration,
            options=options,
            model=model,
            proposition_definitions=definitions,
            goals=tuple(goals),
            goal_labels=labels,
            solver=solver,
            algorithm=algorithm,
        )

    @staticmethod
    def _select_solver(model, goals, definitions):
        dynamic_type = check_dynamics(model)
        requires_dreal = any(
            expression_requires_dreal(substitution(goal.get_formula(), definitions))
            for goal in goals
        )
        if dynamic_type == "ode" or model_requires_dreal(model) or requires_dreal:
            return "dreal"
        return "yices"


class GoalExecutor:
    """Execute selected goals and report their user-facing outcomes."""

    def execute(self, prepared, printer):
        options = prepared.options
        printer.verbose = options.verbose
        for original_goal in prepared.goals:
            label = prepared.goal_labels.get(
                original_goal.get_formula(), "unlabeled"
            )
            if options.goal_labels and label not in options.goal_labels:
                continue
            goal = reach_goal(original_goal) if options.reach else original_goal
            try:
                self._execute_goal(prepared, goal, label, printer)
            finally:
                # Encoding builds solver-specific Boolean abstractions on the
                # model. A witness may return before an algorithm's per-bound
                # cleanup, so no goal may hand that state to the next goal.
                prepared.model.clear()

    def _execute_goal(self, prepared, goal, label, printer):
        options = prepared.options
        formula = substitution(
            goal.get_formula(), prepared.proposition_definitions
        )
        is_reach = isinstance(goal, ReachGoal)
        if is_reach:
            validate_reach_formula(formula)
        validate_formula_solver_support(options.solver, formula)

        algorithm_name = (
            "two-step reachability" if options.two_step and is_reach
            else "two-step" if options.two_step
            else "reachability" if is_reach
            else "one-step"
        )
        printer.run_started(
            prepared.file_name, label, options.solver, algorithm_name,
            options.two_step and options.parallel, options.parallel_core,
            options.bound,
            "mode changes" if is_reach else "mode changes + STL variable points",
            options.time_bound, options.threshold,
            "reachability goal" if is_reach else "negated goal (counterexample search)",
        )

        algorithm = prepared.algorithm
        algorithm.set_debug("{}_{}_{}".format(
            os.path.basename(prepared.file_name), label, options.solver
        ))
        started = time.monotonic()
        try:
            raw_result = algorithm.run(
                prepared.model, goal, prepared.proposition_definitions,
                prepared.configuration, prepared.solver, printer,
            )
        except BaseException:
            printer.clear_progress()
            runner = getattr(algorithm, "runner", None)
            if runner is not None:
                runner.kill_all()
            raise
        elapsed = time.monotonic() - started

        if isinstance(raw_result, AlgorithmResult):
            result = raw_result
            outcome = interpret_algorithm_result(result.status, is_reach)
            finished_bound = result.finished_bound
            assignment = result.assignment
        else:
            legacy_status, _, finished_bound, assignment = raw_result
            outcome = interpret_algorithm_result(legacy_status, is_reach)

        artifact_file = None
        artifact_config = None
        if outcome.has_witness and options.visualize:
            artifact_file, artifact_config = write_verification_artifacts(
                prepared.file_name, finished_bound, label, options.solver,
                is_reach, assignment, prepared.model,
                prepared.proposition_definitions, goal, options.threshold,
            )
        scope = ("at bound {}" if outcome.has_witness else "up to bound {}").format(
            finished_bound
        )
        printer.run_finished(
            outcome.status, finished_bound, elapsed, formula, scope,
            artifact_file, artifact_config,
            (
                "no counterexample in the bounded search; rho >= {}, with "
                "strict robustness guaranteed below that threshold".format(
                    options.threshold
                )
                if outcome.status == "satisfied" else None
            ),
        )


class VerificationWorkflow:
    """Top-level use case independent of CLI and driver construction."""

    def __init__(self, preparer=None, executor=None):
        self.preparer = preparer or RunPreparer()
        self.executor = executor or GoalExecutor()

    def run(self, command, printer):
        try:
            command.parse()
            prepared = self.preparer.prepare(
                command.file, command.config, command.update_solver_config
            )
            self.executor.execute(prepared, printer)
        except SyntaxError as error:
            raise ParsingError(str(error)) from error
