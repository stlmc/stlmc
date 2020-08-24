import abc
import os

from stlmcPy.constraints.constraints import And
from stlmcPy.constraints.operations import make_boolean_abstract_consts, substitutionSize
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.objects.object_builder import generate_object

from timeit import default_timer as timer

from stlmcPy.tree.operations import size_of_tree

import argparse

from stlmcPy.solver.solver_factory import SolverFactory
from stlmcPy.util.logger import Logger


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
        # self.parser.add_argument('-step', '-s', type=int,
        #                          help='objects checking at intervals of step in (lower, upper) (default: 1)')
        # self.parser.add_argument('-timebound', '-tb', type=int,
        #                          help='set time bound of objects checking (default: 60)')
        # self.parser.add_argument('-multithread', '-multy', type=self.str2bool,
        #                          help='run the given objects using multithread (default: false)')
        # TODO: move hylaa-reduction, hylaa-unsat core to hylaa strategy option
        self.parser.add_argument('-solver', type=str,
                                 help='run the objects using given smt solver, support \" {yices, z3, hylaa, hylaa-reduction, hylaa-unsat-core} \" (default: z3)')
        self.parser.add_argument('-ce', type=string_to_bool,
                                 help='generate counter example (default: false)')
        # self.parser.add_argument('-logic', type=str,
        #                          help='run the SMT solver using given given logic (default: QF-NRA)')
        # self.parser.add_argument('-visualize', type=self.str2bool,
        #                          help='if a objects have a counterexample, generate json format file for the trace of the counterexample (default: false)')
        # self.parser.add_argument('-log', type=self.str2bool,
        #                          help='save results of execution in report.txt (default: false)')
        # self.parser.add_argument('-onlySTL', type=self.str2bool,
        #                          help='consider only STL constraints (default: false)')
        self.parser.add_argument('-delta', type=float,
                                 help='delta for invariant condition (default: 0)')
        self._args = None
        self._file_list = list()
        self._lower = 1
        self._upper = 1
        self._solver = "z3"
        self._solver_list = ["z3", "hylaa", "yices", "hylaa-unsat-core", "hylaa-reduction"]
        self._gen_ce = False

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
        if self._args.solver is not None:
            self._solver = (self._args.solver.lower() if self._args.solver.lower() in self._solver_list else 'z3')
        if self._args.ce is not None:
            self._gen_ce = self._args.ce

    @property
    def file_list(self):
        return self._file_list

    @property
    def bound(self):
        return range(self._lower, self._upper + 1)

    @property
    def solver(self):
        return self._solver

    @property
    def is_generate_counterexample(self):
        return self._gen_ce


class Runner(Logger):
    @abc.abstractmethod
    def run(self, config: StlConfiguration):
        solver = SolverFactory(config.solver).generate_solver()
        for file_name in config.file_list:
            #self.add_log_info("Model : \"" + str(file_name) + "\"")
            model, PD, goals = generate_object(file_name)
            for bound in config.bound:
                solver.clear_log()
                for goal in goals:
                    # if bound == 0:
                    # solver.write_to_file(str(file_name) + "_###" + str(goal.get_formula()) + "_###" + config.solver + ".csv")
                    print("======================================")
                    print(str(file_name) + "_###" + str(goal.get_formula()) + "_###" + config.solver + "_" + str(bound))
                    solver.add_bound(bound)
                    # print("start model const")
                    model_const = model.make_consts(bound)
                    # print("end model const")
                    goal_const, goal_boolean_abstract = goal.make_consts(bound, 60, 0.1, model, PD)
                    # print("what is goal_const")
                    # print(goal_const)
                    # print(goal_boolean_abstract)

                    boolean_abstract = dict()
                    boolean_abstract.update(model.boolean_abstract)
                    boolean_abstract.update(goal_boolean_abstract)
                    boolean_abstract_consts = make_boolean_abstract_consts(boolean_abstract)

                    solve_start = timer()
                    result, size = solver.solve(And([model_const, goal_const, boolean_abstract_consts]),
                                                model.range_dict, boolean_abstract)
                    # result, size = solver.solve(And([goal_const, boolean_abstract_consts]), model.range_dict, boolean_abstract)
                    # result, size = solver.solve(And([model_const, boolean_abstract_consts]), model.range_dict, boolean_abstract)

                    solve_end = timer()
                    self.concat(solver.get_log_info())
                    print("Driver returns : " + str(result) + ", Total solving time : " + str(solve_end - solve_start))
                    print(str(file_name) + "_###" + str(goal.get_formula()) + "_###" + config.solver + "_" + str(bound))
                    model.clear()
                    goal.clear()
                    print("======================================")

                    solver.add_result(result)
                    solver.add_log_info()
                    # self.add_log_info("goal: " + str(goal.get_formula()) + ", result: " + str(result))
                    if config.is_generate_counterexample:
                        assignment = solver.make_assignment()
                        assignment.get_assignments()
                    solver.append_to_file(
                        str(file_name) + "_#" + str(goal.get_formula()) + "_#" + config.solver + "_#" + str(
                            bound) + ".csv")
                    # print(assignment)
                    # if is_visualize:
                    # integrals_list = model.get_flow_for_assignment(1)
                    # assignment = solver.make_assignment()
                    # print(assignment.get_assignments())
                    # print(result)


class DriverFactory:
    def __init__(self):
        pass

    @abc.abstractmethod
    def make_config(self):
        return StlConfiguration()

    @abc.abstractmethod
    def make_runner(self):
        return Runner()
