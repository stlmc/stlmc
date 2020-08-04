import abc
import os

from stlmcPy.constraints.constraints import And
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.objects.object_builder import generate_object

import argparse

from stlmcPy.solver.solver_factory import SolverFactory


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

    @property
    def file_list(self):
        return self._file_list

    @property
    def bound(self):
        return range(self._lower, self._upper + 1)

    @property
    def solver(self):
        return self._solver


class Runner:
    @staticmethod
    def run(config: StlConfiguration):
        for file_name in config.file_list:
            model, PD, goals = generate_object(file_name)
            for bound in config.bound:
                model_const = model.make_consts(bound)
                solver = SolverFactory(config.solver).generate_solver()
                for goal in goals:
                    goal_const = goal.make_consts(bound, 60, 0, model, PD)
                    result, size = solver.solve(And([model_const, goal_const]), model.range_dict)
                    print(result)
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
