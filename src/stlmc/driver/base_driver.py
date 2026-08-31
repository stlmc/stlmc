import os.path
import sys
import time

from ..driver.abstract_driver import DriverFactory, CmdParser, Runner
from ..cli.parser import build_parser
from ..config_schema import resolve_parallel_core
from ..constraints.operations import substitution
from ..application.result import interpret_algorithm_result
from ..artifacts.writer import write_verification_artifacts
from ..exceptions import (
    IllegalArgumentError, NotSupportedError, ParsingError,
    SolverUnavailableError,
)
from ..application.algorithm_factory import AlgorithmFactory
from ..objects.configuration import Configuration
from ..objects.goal import (
    Goal, ReachGoal, optimize, reach_goal, validate_reach_formula,
)
from ..objects.model import Model
from ..application.model_loader import ObjectManager
from ..parser.checker import check_dynamics, check_validity
from ..parser.config_visitor import ConfigVisitor
from ..parser.model_visitor import ModelVisitor
from ..solver.availability import find_dreal
from ..solver.solver_factory import SolverFactory
from ..solver.capability import (
    expression_requires_dreal,
    model_requires_dreal,
    validate_formula_solver_support,
    validate_model_solver_support,
)
from ..utils.print import Printer


def validate_requested_goal_labels(requested_labels, goal_labels):
    available_labels = sorted(set(goal_labels.values()))
    missing_labels = sorted(set(requested_labels).difference(available_labels))
    if not missing_labels:
        return

    available = ", ".join(available_labels) if available_labels else "none"
    raise IllegalArgumentError(
        "unknown goal label(s): {}; available goals: {}".format(
            ", ".join(missing_labels), available
        )
    )


class BaseDriverFactory(DriverFactory):
    def __init__(self):
        super().__init__()

    def make_config_parser(self) -> ConfigVisitor:
        return ConfigVisitor()

    def make_model_parser(self) -> ModelVisitor:
        return ModelVisitor()

    def make_cmd_parser(self) -> CmdParser:
        return BaseCmdParser()

    def make_runner(self) -> Runner:
        return BaseRunner()

    def make_printer(self) -> Printer:
        return Printer()


class BaseCmdParser(CmdParser):
    def __init__(self):
        self.config_visitor = ConfigVisitor()
        self.config = Configuration()
        self.built_in_names = ["file", "model_cfg", "model_specific_cfg"]

        self.parser = build_parser()
        self.arg_value_dict = dict()
        self.file = ""

    def update_solver_config(self, underlying_solver):
        common_section = self.config.get_section(underlying_solver)
        for arg_name in self.config_visitor.section_argument_dict[underlying_solver]:
            if arg_name in self.arg_value_dict:
                # assume all arguments in the solver section are string types
                common_section.arguments[arg_name] = "\"{}\"".format(self.arg_value_dict[arg_name])
                del self.arg_value_dict[arg_name]

        for arg_name in self.config_visitor.section_boolean_argument_dict[underlying_solver]:
            if arg_name in self.arg_value_dict:
                # assume all arguments in the solver section are string types
                # if cmd is set to default (i.e., false), follow the configuration file
                if self.arg_value_dict[arg_name] != "false":
                    common_section.arguments[arg_name] = "\"{}\"".format(self.arg_value_dict[arg_name])
                del self.arg_value_dict[arg_name]

    def parse(self):
        args = self.parser.parse_args()
        if args.file is None:
            raise ValueError("should provide an STLmc model file path")

        if not os.path.exists(args.file):
            raise ValueError("\"{}\" is not a valid STLmc model file path".format(args.file))

        if not os.path.isfile(args.file):
            raise ValueError("\"{}\" is not a file (please provide an STLmc model \"file\")".format(args.file))

        if args.default_cfg is not None:
            self.config = self.config_visitor.parse_from_file(args.default_cfg)
        else:
            package_dir = os.path.dirname(os.path.dirname(__file__))
            self.config = self.config_visitor.parse_from_file(
                os.path.join(package_dir, "default.cfg")
            )
            
            dreal = self.config.get_section("dreal")
            exec_path = dreal.get_value("executable-path")
            if exec_path == "dReal":
                exec_path = find_dreal() or exec_path
            dreal.set_value("executable-path", exec_path)

        if args.model_cfg is not None:
            if not os.path.exists(args.model_cfg):
                raise NotSupportedError("model config \"{}\" does not exist".format(args.model_cfg))
            # model_cfg
            self.config = self.config_visitor.parse_from_file(args.model_cfg, self.config)
        else:
            model_cfg_name = "{}/{}.cfg".format(os.path.dirname(args.file),
                                                os.path.basename(args.file).split(".")[0])
            if os.path.exists(model_cfg_name):
                self.config = self.config_visitor.parse_from_file(model_cfg_name, self.config)

        if args.model_specific_cfg is not None:
            if not os.path.exists(args.model_specific_cfg):
                raise NotSupportedError("model specific config \"{}\" does not exist".format(args.model_specific_cfg))
            # model_specific_cfg
            self.config = self.config_visitor.parse_from_file(args.model_specific_cfg, self.config)

        # print(self.config)
        for key in args.__dict__:
            value = args.__dict__[key]
            if key in self.built_in_names:
                if key == "file":
                    self.file = value
            else:
                if value is not None:
                    key = key.replace("_", "-")
                    if key not in {"logic", "smt2-dir", "executable-path"}:
                        value = str(value).lower()

                    self.arg_value_dict[key] = value

        # update the common section first
        common_section = self.config.get_section("common")
        for arg_name in self.config_visitor.section_argument_dict["common"]:
            if arg_name in self.arg_value_dict:
                common_section.arguments[arg_name] = self.arg_value_dict[arg_name]
                del self.arg_value_dict[arg_name]

        for arg_name in self.config_visitor.section_boolean_argument_dict["common"]:
            if arg_name in self.arg_value_dict:
                # if cmd is set to default (i.e., false), follow the configuration file
                if self.arg_value_dict[arg_name] != "false":
                    common_section.arguments[arg_name] = self.arg_value_dict[arg_name]
                del self.arg_value_dict[arg_name]

        # update solver specific section
        underlying_solver = common_section.get_value("solver")
        valid_solver = ["cvc5", "yices", "z3", "dreal", "auto"]
        if underlying_solver not in valid_solver:
            raise ValueError("\"{}\" is not a valid SMT solver".format(underlying_solver))

        if underlying_solver != "auto":
            self.update_solver_config(underlying_solver)

        missing_dict = self.config_visitor.get_missing_arguments(self.config)
        for ordered_section_name in self.config_visitor.section_names:
            if ordered_section_name in missing_dict:
                added = set()
                missing = missing_dict[ordered_section_name]
                for missing_arg_name in missing:
                    if missing_arg_name in self.arg_value_dict:
                        section = self.config.get_section(ordered_section_name)
                        section.arguments[missing_arg_name] = self.arg_value_dict[missing_arg_name]
                        added.add(missing_arg_name)

                missing.difference_update(added)

                if len(missing) > 0:
                    del missing_dict[ordered_section_name]

        missing_dict = self.config_visitor.get_missing_arguments(self.config)
        for section_name in missing_dict:
            if section_name == underlying_solver:
                raise IllegalArgumentError("should give the following arguments in order to run:\n  {}".format(
                    ",".join(missing_dict[section_name])))
            print("warning: a section \"{}\" has missing arguments ({})".format(section_name,
                                                                                ",".join(missing_dict[section_name])))
        self.config.check_mandatory()


class BaseRunner(Runner):
    def run(self, config_parser: ConfigVisitor, model_parser: ModelVisitor,
            cmd_parser: CmdParser, printer: Printer):
        try:
            sys.setrecursionlimit(1000000)

            # parsing configurations
            cmd_parser.parse()
            config = cmd_parser.config

            common_section = config.get_section("common")
            underlying_solver = common_section.get_value("solver")
            bound = common_section.get_value("bound")
            time_bound = common_section.get_value("time-bound")
            delta = common_section.get_value("threshold")
            time_horizon = common_section.get_value("time-horizon")

            if time_horizon == "time-bound":
                common_section.set_value("time-horizon", time_bound)
            common_section.set_value(
                "parallel-core",
                resolve_parallel_core(common_section.get_value("parallel-core")),
            )

            reach_goal_opt = common_section.get_value("reach")
            gen_result = common_section.get_value("visualize")
            print_type = common_section.get_value("verbose")

            is_formula_label = common_section.is_argument_in("goal")

            f_labels = list()
            if is_formula_label:
                f_label_raw = common_section.get_value("goal")
                f_labels = [label.strip() for label in f_label_raw.split(",")]
                if len(f_labels) > 1:
                    for f_label in f_labels:
                        if f_label == "all":
                            raise NotSupportedError("\"all\" and other labels \"{}\" cannot be used together "
                                                    "(set only \"all\" or set labels without \"all\")"
                                                    .format(" , ".join(f_labels)))
                elif len(f_labels) == 1:
                    if f_labels[0] == "all":
                        f_labels = list()

            file_name = cmd_parser.file

            object_manager = ObjectManager()

            if print_type == "true":
                printer.verbose = True

            model, PD, goals, goal_labels = object_manager.generate_objects(file_name)
            validate_requested_goal_labels(f_labels, goal_labels)
            if underlying_solver == "auto":
                dynamic_type = check_dynamics(model)
                formulas_require_dreal = any(
                    expression_requires_dreal(
                        substitution(goal.get_formula(), PD)
                    )
                    for goal in goals
                )
                if (
                    dynamic_type == "ode"
                    or model_requires_dreal(model)
                    or formulas_require_dreal
                ):
                    common_section.set_value("solver", "dreal")
                    underlying_solver = "dreal"
                else:
                    common_section.set_value("solver", "yices")
                    yices_section = config.get_section("yices")
                    underlying_solver = "yices"
                    if dynamic_type == "poly":
                        yices_section.set_value("logic", "QF_NRA")
                    else:
                        yices_section.set_value("logic", "QF_LRA")
            cmd_parser.update_solver_config(underlying_solver)
            check_validity(config)
            underlying_solver = common_section.get_value("solver")
            validate_model_solver_support(underlying_solver, model)

            solver_factory = SolverFactory()
            solver = solver_factory.generate_solver(config)
            algorithm = AlgorithmFactory(
                config, solver_factory.generate_formula_solver_factory()
            ).generate()

            for goal in goals:
                if len(f_labels) > 0:
                    g_formula = goal.get_formula()
                    # invalid
                    if g_formula not in goal_labels:
                        raise NotSupportedError("goal labeling error")
                    # match
                    if goal_labels[g_formula] not in f_labels:
                        continue

                if reach_goal_opt == "true":
                    goal = reach_goal(goal)

                label = "unlabeled"
                if goal.get_formula() in goal_labels:
                    label = goal_labels[goal.get_formula()]

                formula_string = substitution(goal.get_formula(), PD)
                if isinstance(goal, ReachGoal):
                    validate_reach_formula(formula_string)
                validate_formula_solver_support(underlying_solver, formula_string)
                is_two_step = common_section.get_value("two-step") == "true"
                is_parallel = (
                    is_two_step
                    and common_section.get_value("parallel") == "true"
                )
                parallel_core = int(common_section.get_value("parallel-core"))
                is_reach_query = isinstance(goal, ReachGoal)
                if is_two_step:
                    algorithm_name = (
                        "two-step reachability"
                        if is_reach_query else "two-step"
                    )
                elif is_reach_query:
                    algorithm_name = "reachability"
                else:
                    algorithm_name = "one-step"
                printer.run_started(
                    file_name, label, underlying_solver, algorithm_name,
                    is_parallel, parallel_core, bound,
                    (
                        "mode changes"
                        if is_reach_query
                        else "mode changes + STL variable points"
                    ),
                    time_bound, delta,
                    (
                        "reachability goal"
                        if is_reach_query
                        else "negated goal (counterexample search)"
                    ),
                )

                time_start = time.monotonic()
                algorithm.set_debug("{}_{}_{}".format(os.path.basename(file_name), label, underlying_solver))
                try:
                    final_result, total_time, finished_bound, assn_dict = algorithm.run(
                        model, goal, PD, config, solver, printer
                    )
                except BaseException:
                    printer.clear_progress()
                    runner = getattr(algorithm, "runner", None)
                    if runner is not None:
                        runner.kill_all()
                    raise
                time_end = time.monotonic()
                total_time = time_end - time_start

                outcome = interpret_algorithm_result(
                    final_result, is_reach_query
                )
                status = outcome.status
                counterexample_file = None
                visual_config_file = None
                found_witness = outcome.has_witness
                if found_witness and gen_result == "true":
                    counterexample_file, visual_config_file = (
                        write_verification_artifacts(
                            file_name, finished_bound, label,
                            underlying_solver, is_reach_query, assn_dict,
                            model, PD, goal, delta,
                        )
                    )
                result_scope = (
                    "at bound {}" if found_witness else "up to bound {}"
                ).format(finished_bound)
                printer.run_finished(
                    status, finished_bound, total_time, formula_string,
                    result_scope, counterexample_file, visual_config_file,
                    (
                        "no counterexample in the bounded search; "
                        "rho >= {}, with strict robustness guaranteed below "
                        "that threshold".format(delta)
                        if status == "satisfied" else None
                    ),
                )
        except (NotSupportedError, IllegalArgumentError, SolverUnavailableError):
            raise
        except SyntaxError as e:
            raise ParsingError(str(e)) from e
