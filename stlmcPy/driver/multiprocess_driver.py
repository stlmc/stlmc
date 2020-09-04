from stlmcPy.constraints.constraints import And
from stlmcPy.constraints.operations import make_boolean_abstract_consts
from stlmcPy.objects.object_factory import ObjectFactory
from stlmcPy.solver.solver_factory import SolverFactory
from stlmcPy.util.print import Printer
from .base_driver import DriverFactory, StlConfiguration, Runner, StlModelChecker
from ..util.logger import Logger


def unit_run(arg: dict):
    mul_runner = arg["runner"]
    cur_bound = arg["bound"]
    output_file_name = arg["output_file_name"]
    output_file_name_bound = arg["output_file_name_bound"]
    solver = arg["solver"]
    solver_name = arg["solver_name"]
    model = arg["model"]
    goal = arg["goal"]
    PD = arg["prop dict"]
    logger = arg["logger"]
    printer = arg["printer"]

    logger.set_output_file_name(output_file_name_bound)
    logger.write_to_csv(overwrite=True)

    logger.reset_timer()
    logger.start_timer("goal timer")
    logger.add_info("bound", cur_bound)

    model_const = model.make_consts(cur_bound)
    goal_const, goal_boolean_abstract = goal.make_consts(cur_bound, 60, 1, model, PD)

    boolean_abstract = dict()
    boolean_abstract.update(model.boolean_abstract)
    boolean_abstract.update(goal_boolean_abstract)
    boolean_abstract_consts = make_boolean_abstract_consts(boolean_abstract)

    printer.print_normal("> {}".format(solver_name))
    result, size = solver.solve(And([model_const, goal_const, boolean_abstract_consts]),
                                model.range_dict, boolean_abstract)

    logger.stop_timer("goal timer")
    printer.print_normal_dark("\n> result")
    printer.print_normal_dark("Driver returns : {}, Total solving time : {}".format(result,
                                                                                    logger.get_duration_time(
                                                                                        "goal timer")))
    printer.print_normal_dark("formula : {}, bound : {}".format(goal.get_formula(), cur_bound))
    printer.print_line()

    logger.add_info("result", result)
    logger.add_info("total", logger.get_duration_time("goal timer"))
    logger.write_to_csv(clear_after_write=False)
    logger.write_to_csv(file_name=output_file_name, cols=["total", "result"])
    model.clear()
    goal.clear()


class MultiprocessRunner(Runner):
    def __init__(self):
        super().__init__()
        self.jobs = []
        self.arguments = []

    def run(self, config: StlConfiguration, logger: Logger, printer: Printer):
        Printer.verbose_on = config.verbose_flag
        Printer.debug_on = config.debug_flag

        object_manager = ObjectFactory(config.encoding).generate_object_manager()

        for file_name in config.file_list:
            model, PD, goals = object_manager.generate_objects(file_name)
            for goal in goals:
                output_file_name = "{}_###{}_###{}_###{}".format(file_name, goal.get_formula(), config.solver, config.encoding)
                logger.write_to_csv(file_name=output_file_name, overwrite=True)
                for bound in config.bound:
                    output_file_name_bound = "{}_{}".format(output_file_name, bound)

                    thread_logger = Logger()
                    thread_solver = SolverFactory(config.solver).generate_solver()
                    thread_solver.append_logger(thread_logger)

                    # apply every optimization
                    for opt in config.optimize_flags:
                        thread_solver.set_optimize_flag(opt, True)

                    info_dict = dict()
                    info_dict["runner"] = self
                    info_dict["bound"] = bound
                    info_dict["output_file_name"] = output_file_name
                    info_dict["output_file_name_bound"] = output_file_name_bound
                    info_dict["solver"] = thread_solver
                    info_dict["solver_name"] = config.solver
                    info_dict["model"] = model
                    info_dict["goal"] = goal
                    info_dict["prop dict"] = PD
                    info_dict["logger"] = thread_logger
                    info_dict["printer"] = printer

                    self.arguments.append(info_dict)
        printer.print_verbose("multiprocess arguments: {}".format(str(len(self.arguments))))


class MultiprocessDriverFactory(DriverFactory):
    def __init__(self):
        super().__init__()

    def make_config(self):
        return StlConfiguration()

    def make_runner(self):
        return MultiprocessRunner()

    def make_logger(self):
        return Logger()

    def make_printer(self):
        return Printer()


class MultiprocessStlModelChecker(StlModelChecker):
    def __init__(self):
        super().__init__()

    def get_args(self):
        return self.runner.arguments
