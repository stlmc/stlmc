import abc
import argparse
import os

from stlmcPy.constraints.constraints import And
from stlmcPy.constraints.operations import make_boolean_abstract_consts
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.objects.object_factory import ObjectFactory
from stlmcPy.solver.solver_factory import SolverFactory
from stlmcPy.util.logger import Logger
from stlmcPy.util.print import Printer
from timeit import default_timer as timer


def string_to_bool(v: str):
    if v.lower() in ('yes', 'true', 't', 'y', '1'):
        return True
    elif v.lower() in ('no', 'false', 'f', 'n', '0'):
        return False
    else:
        raise argparse.ArgumentTypeError('Boolean value expected.')


def print_result(modelName, formula, result, k, tauMax, cSize, fSize, generationTime, solvingTime, totalTime):
    print("---------------------------------------------------------------------------\n")
    print("Model : \"" + str(modelName) + "\", STL formula : \"" + formula + "\"")
    print("Result : " + result + ", Variable point bound : " + str(k) + ", Time bound : " + str(tauMax))
    print("Execution Time(sec) : " + totalTime + "\n")
    print("---------------------------------------------------------------------------\n")


class StlConfiguration:
    def __init__(self):
        self.parser = argparse.ArgumentParser(description='For more information. See below:')
        self.parser.add_argument('file', nargs='?', type=str, help="Type file or directory to process")
        self.parser.add_argument('-lower', '-l', type=int,
                                 help='objects checking from the given lower bound (default: 1)')
        self.parser.add_argument('-upper', '-u', type=int,
                                 help='objects checking upto given upper bound (default: lower_bound)')
        self.parser.add_argument('-step', '-s', type=int,
                                 help='objects checking at intervals of step in (lower, upper) (default: 1)')
        self.parser.add_argument('-timebound', '-tb', type=int,
                                  help='set time bound of objects checking (default: 60)')
        # self.parser.add_argument('-multithread', '-multy', type=self.str2bool,
        #                          help='run the given objects using multithread (default: false)')
        # TODO: move hylaa-reduction, hylaa-unsat core to hylaa strategy option
        self.parser.add_argument('-solver', type=str,
                                 help='run the objects using given smt solver, support \" {yices, dreal, z3, hylaa, hylaa-reduction, hylaa-unsat-core} \" (default: z3)')
        self.parser.add_argument('-optimize', type=str,
                                 help='turn on solver optimization, support \" {formula} \" (default: None)')
        self.parser.add_argument('-formula_encoding', type=str,
                                 help='select formula encoding, support \" {model-with-goal, model-with-goal-enhanced, only-goal-stl, only-goal-stl-enhanced} \" (default: model-with-goal-enhanced)')
        self.parser.add_argument('-ce', type=string_to_bool,
                                 help='generate counter example (default: false)')
        self.parser.add_argument('-verbose', type=string_to_bool,
                                 help='turn on verbose message logging (default: false)')
        self.parser.add_argument('-debug', type=string_to_bool,
                                 help='turn on debug message logging (default: false)')
        self.parser.add_argument('-delta', type=float,
                                 help='delta for invariant condition (default: 0)')
        self._args = None
        self._file_list = list()
        self._lower = 1
        self._upper = 1
        self._step = 1
        self._solver = "z3"
        self._optimize_flags = list()
        self._solver_list = ["z3", "dreal", "yices"]
        self._formula_encoding = "model-with-goal-enhanced"
        self._formula_encoding_list = ["model-with-goal-enhanced", "model-with-goal", "only-goal-stl", "only-goal-stl-enhanced"]
        self._gen_ce = False
        self._verbose = False
        self._debug = False
        self._timebound = 1

    def parse(self):
        self._args = self.parser.parse_args()

        # check if given arg is file or directory
        if os.path.isdir(self._args.file):
            file_list = os.listdir(self._args.file)
            for item in file_list:
                if os.path.splitext(item)[-1].lower() == ".model":
                    self._file_list.append(os.path.abspath(self._args.file) + "/" + item)
        elif os.path.isfile(self._args.file):
            self._file_list.append(self._args.file)
        else:
            raise NotSupportedError("argument parsing error")

        if self._args.lower is not None:
            self._lower = self._args.lower
        if self._args.upper is not None:
            self._upper = self._args.upper
        if self._args.step is not None:
            self._step = self._args.step
        if self._args.solver is not None:
            self._solver = (self._args.solver.lower() if self._args.solver.lower() in self._solver_list else 'z3')
        if self._args.optimize is not None:
            self._optimize_flags = self._args.optimize.split(',')
        if self._args.ce is not None:
            self._gen_ce = self._args.ce
        if self._args.formula_encoding is not None:
            self._formula_encoding = (self._args.formula_encoding.lower() if self._args.formula_encoding.lower() in self._formula_encoding_list else "model-with-goal-enhanced")
        if self._args.verbose is not None:
            self._verbose = self._args.verbose
        if self._args.debug is not None:
            self._debug = self._args.debug
        if self._args.timebound is not None:
            self._timebound = self._args.timebound

    @property
    def file_list(self):
        return self._file_list

    @property
    def bound(self):
        return range(self._lower, self._upper + 1, self._step)

    @property
    def optimize_flags(self):
        return self._optimize_flags

    @property
    def solver(self):
        return self._solver

    @property
    def timebound(self):
        return self._timebound

    @property
    def encoding(self):
        return self._formula_encoding

    @property
    def debug_flag(self):
        return self._debug

    @property
    def verbose_flag(self):
        return self._verbose

    @property
    def is_generate_counterexample(self):
        return self._gen_ce


class Runner:
    @abc.abstractmethod
    def run(self, config: StlConfiguration, logger: Logger, printer: Printer):
        object_manager = ObjectFactory(config.encoding).generate_object_manager()
        solver = SolverFactory(config.solver).generate_solver()
        solver.append_logger(logger)

        # apply every optimization
        for opt in config.optimize_flags:
            solver.set_optimize_flag(opt, True)

        Printer.debug_on = config.debug_flag
        Printer.verbose_on = config.verbose_flag
        for file_name in config.file_list:
            model, PD, goals = object_manager.generate_objects(file_name)
            
            for goal in goals:
                output_file_name = "{}_###{}_###{}_###{}".format(file_name, goal.get_formula(), config.solver, config.encoding)
                logger.write_to_csv(file_name=output_file_name, overwrite=True)
                key_index = file_name.rfind("/")
                stl_file_name = str(file_name[key_index+1:]) + "_" + str(goal.get_formula()) + "_" + config.solver + "_" + config.encoding
                for bound in config.bound:
                    output_file_name_bound = "{}_{}".format(output_file_name, bound)
                    logger.set_output_file_name(output_file_name_bound)
                    logger.write_to_csv(overwrite=True)

                    # start logging
                    logger.reset_timer()
                    logger.start_timer("goal timer")
                    logger.add_info("bound", bound)

                    model_const = model.make_consts(bound)
                    s_time = timer()
                    
                    goal_const, goal_boolean_abstract = goal.make_consts(bound, config.timebound, 0, model, PD)
                    
                    boolean_abstract = dict()
                    boolean_abstract.update(model.boolean_abstract)
                    boolean_abstract.update(goal_boolean_abstract)
                    boolean_abstract_consts = make_boolean_abstract_consts(boolean_abstract)
                    e_time = timer()
                    
                    printer.print_normal("> {}".format(config.solver))
                    result, size = solver.solve(And([model_const, goal_const, boolean_abstract_consts]),
                                                model.range_dict, boolean_abstract)
                    e_time2 = timer()

                    if not os.path.exists(stl_file_name + ".csv"):
                        with open(stl_file_name + ".csv", 'a') as csv_file:
                            csv_file.write("formula,bound,size,goal_generation_time,smt_solving_time,result\n")
                            csv_file.write(str(goal.get_formula()) + "," + str(bound) + "," +  str(size) + "," + str(e_time-s_time) + "," + str(e_time2-e_time) + "," + str(result) + "\n")
                    else:
                        with open(stl_file_name + ".csv", 'a') as csv_file:
                            csv_file.write(str(goal.get_formula()) + "," +str(bound) + "," + str(size) + "," + str(e_time-s_time) + "," + str(e_time2-e_time) + "," + str(result) + "\n")


                    logger.stop_timer("goal timer")
                    printer.print_normal_dark("\n> result")
                    printer.print_normal_dark("Driver returns : {}, Total solving time : {}".format(result,
                                                                                                    logger.get_duration_time(
                                                                                                        "goal timer")))
                    printer.print_normal_dark("formula : {}, bound : {}".format(goal.get_formula(), bound))
                    printer.print_line()

                    logger.add_info("result", result)
                    logger.add_info("total", logger.get_duration_time("goal timer"))
                    logger.write_to_csv(clear_after_write=False)
                    logger.write_to_csv(file_name=output_file_name, cols=["total", "result"])


                    model.clear()
                    goal.clear()
                    solver.clear()

                    if config.is_generate_counterexample:
                        assignment = solver.make_assignment()
                        assignment.get_assignments()


class DriverFactory:
    def __init__(self):
        pass

    @abc.abstractmethod
    def make_config(self):
        return StlConfiguration()

    @abc.abstractmethod
    def make_runner(self):
        return Runner()

    @abc.abstractmethod
    def make_logger(self):
        return Logger()

    @abc.abstractmethod
    def make_printer(self):
        return Printer()


class StlModelChecker:
    def __init__(self):
        self.config = None
        self.runner = None
        self.logger = None
        self.printer = None

    def create_simulation_env(self, df: DriverFactory):
        self.config = df.make_config()
        self.runner = df.make_runner()
        self.logger = df.make_logger()
        self.printer = df.make_printer()

    def run(self):
        self.config.parse()
        self.runner.run(self.config, self.logger, self.printer)
