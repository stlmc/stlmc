from stlmcPy.objects.object_factory import ObjectFactory
import subprocess
import sys
import time
import traceback

import stlmcPy
from stlmcPy.DataGenerator import *
import os
import multiprocessing
import argparse

from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.objects.goal import Goal
from stlmcPy.parser.model_visitor import ModelVisitor
from stlmcPy.result.result import TrueResult, FalseResult
from stlmcPy.solver.solver_factory import SolverFactory


class Driver:
    def __init__(self):
        pass
        # self.parser = argparse.ArgumentParser(description='For more information. See below:')
        # self.parser.add_argument('file', nargs='?', type=str, help="Type file or directory to process")
        # self.parser.add_argument('-lower', '-l', type=int,
        #                          help='objects checking from the given lower bound (default: 1)')
        # self.parser.add_argument('-upper', '-u', type=int,
        #                          help='objects checking upto given upper bound (default: lower_bound)')
        # self.parser.add_argument('-step', '-s', type=int,
        #                          help='objects checking at intervals of step in (lower, upper) (default: 1)')
        # self.parser.add_argument('-timebound', '-tb', type=int,
        #                          help='set time bound of objects checking (default: 60)')
        # self.parser.add_argument('-multithread', '-multy', type=self.str2bool,
        #                          help='run the given objects using multithread (default: false)')
        # self.parser.add_argument('-solver', type=str,
        #                          help='run the objects using given smt solver, support \" {Yices, Z3} \" (default: z3)')
        # self.parser.add_argument('-logic', type=str,
        #                          help='run the SMT solver using given given logic (default: QF-NRA)')
        # self.parser.add_argument('-visualize', type=self.str2bool,
        #                          help='if a objects have a counterexample, generate json format file for the trace of the counterexample (default: false)')
        # self.parser.add_argument('-log', type=self.str2bool,
        #                          help='save results of execution in report.txt (default: false)')
        # self.parser.add_argument('-onlySTL', type=self.str2bool,
        #                          help='consider only STL constraints (default: false)')
        # self.parser.add_argument('-delta', type=float,
        #                          help='delta for invariant condition (default: 0)')
        #
        # self.args = None
        # self.is_print = False

    # def str2bool(self, v: str):
    #     if v.lower() in ('yes', 'true', 't', 'y', '1'):
    #         return True
    #     elif v.lower() in ('no', 'false', 'f', 'n', '0'):
    #         return False
    #     else:
    #         raise argparse.ArgumentTypeError('Boolean value expected.')
    #
    # # an implementation of Algorithm 1 in the paper
    # def model_check1(self, stlModel, modelName, stlFormula, bound, timeBound, solver, logic, onlySTL, delta, goal: Goal,
    #                  iterative=True):
    #     stlModel.strStlFormula = str(stlFormula)
    #     (constSize, fsSize) = (0, 0)
    #     (stim1, etime1, stime2) = (0, 0, 0)
    #     isUnknown = False
    #     negFormula = NotFormula(stlFormula)  # negate the formula
    #     isError = False
    #     solver2 = SolverFactory(solver).generate_solver()
    #     goal.prepare(stlModel.modeVar, stlModel.contVar, stlModel.varVal, stlModel.modeModule, stlModel.init,
    #                  stlModel.prop)
    #     for i in range(0 if iterative else bound, bound + 1):
    #         stime1 = time.process_time()
    #         transConsts, invConsts, flowConsts = stlModel.make_consts(i, delta)
    #         stlConsts, timeConsts, partitionConsts, formulaConst, sizeFromModel = goal.make_consts(i, timeBound, delta)
    #
    #         etime1 = time.process_time()
    #         if onlySTL:
    #             print("only STL is true")
    #             allConsts = partitionConsts + [formulaConst]
    #         elif solver == 'hylaa':
    #             allConsts = [invConsts, formulaConst] + stlConsts + partitionConsts + transConsts
    #
    #             # allConsts = (partitionConsts + [formulaConst], stlConsts + [invConsts] + transConsts)
    #         else:
    #             allConsts = transConsts + [invConsts, flowConsts] + stlConsts + timeConsts + partitionConsts + [
    #                 formulaConst]
    #             # allConsts = stlConsts + partitionConsts + [formulaConst]
    #             # allConsts = [invConsts]
    #         (result, cSize, model) = solver2.solve(allConsts)
    #
    #         stime2 = time.process_time()
    #
    #         # calculate size
    #         # fsSize += sum([ENC.size(f) for f in [fs[0]] + list(fs[1].values())])
    #         fsSize += sizeFromModel
    #         constSize += cSize
    #
    #         generationTime = round((etime1 - stime1), 4)
    #         solvingTime = round((stime2 - etime1), 4)
    #         totalTime = round((stime2 - stime1), 4)
    #     if isError:
    #         return (True, True, True, True, True, True)
    #     if self.is_print:
    #         printResult(modelName, str(stlFormula), str(result), bound, timeBound, constSize, fsSize,
    #                     str(generationTime), str(solvingTime),
    #                     str(totalTime))
    #     return (result, constSize, fsSize, str(generationTime), str(solvingTime), str(totalTime))
    #
    # def printResult(self, modelName, formula, result, k, tauMax, cSize, fSize, generationTime, solvingTime, totalTime):
    #     print("---------------------------------------------------------------------------\n")
    #     print("Model : \"" + str(modelName) + "\", STL formula : \"" + formula + "\"")
    #     print("Result : " + result + ", Variable point bound : " + str(k) + ", Time bound : " + str(tauMax))
    #     print("Execution Time(sec) : " + totalTime + "\n")
    #     print("---------------------------------------------------------------------------\n")
    #
    # def module(self, title, stlModel, formula, k, timeBound, dataGenerator, visualize, resultSave, solver, logic, delta,
    #            onlySTL,
    #            goal: Goal):
    #     modelName = os.path.splitext(os.path.basename(title))[0]
    #     (result, cSize, fSize, generationTime, solvingTime, totalTime) = self.model_check1(stlModel, modelName, formula, k,
    #                                                                                   timeBound, solver, logic,
    #                                                                                   onlySTL,
    #                                                                                   delta, goal, False)
    #
    #     res = None
    #     # TODO: This should be moved into solver.solve method
    #     if result is True:
    #         res = TrueResult()
    #     else:
    #         res = FalseResult()
    #
    #     if isinstance(solvingTime, bool):
    #         raise NotSupportedError("Solving time is not bool type")
    #     if visualize:
    #         dataGenerator.data = stlModel.data
    #         dataGenerator.stackID = modelName
    #         dataGenerator.solver = solver
    #         dataGenerator.result = result
    #         dataGenerator.visualize()
    #     if resultSave:
    #         filename = "report" + "_" + modelName + "_" + str(formula) + "_" + solver + ".csv"
    #         rel_path = str(os.path.abspath(os.curdir)) + "/reports/" + filename
    #         with open(rel_path, 'a+') as fle:
    #             print(",".join([str(k), str(cSize), str(fSize), str(result), generationTime, solvingTime, totalTime]),
    #                   file=fle)
    #     return res

    # def modelCheck(self, params):
    #     fileName = params["model_name"]
    #     lower = params["lower_bound"]
    #     upper = params["upper_bound"]
    #     step = params["step"]
    #     timeBound = params["time_bound"]
    #     visualize = params["is_visualize"]
    #     multy = params["is_multithread"]
    #     resultSave = params["is_save"]
    #     solver = params["solver_type"]
    #     logic = params["logic_type"]
    #     delta = params["delta"]
    #     onlySTL = params["only_stl"]
    #
    #
    #     modelVisitor = ModelVisitor()
    #
    #     stlMC, goals = modelVisitor.get_parse_tree(fileName)
    #     # stlMC =
    #     dataGenerator = Api()
    #     title = fileName
    #     filename = ""
    #     isNormal = True
    #     isTri = False
    #     result = list()
    #
    #     if (isTri and solver == "dreal4") or (not isTri and solver != "dreal4") or solver == "dreal4":
    #         for i in range(len(goals)):
    #             for k in range(lower, upper + 1, step):
    #                 formula = goals[i].formula
    #                 if resultSave:
    #                     modelName = os.path.splitext(os.path.basename(title))[0]
    #                     filename = "report" + "_" + modelName + "_" + str(formula) + "_" + solver + ".csv"
    #                     rel_path = str(os.path.abspath(os.curdir)) + "/reports/" + filename
    #                     if not os.path.isfile(rel_path):
    #                         with open(rel_path, 'w+') as fle:
    #                             print("k,ConstraintSize,TranslationSize,Result,generationTime,solvingTime, totalTime",
    #                                   file=fle)
    #                 if multy:
    #                     # executor.submit(module,
    #                     # title, stlMC, formula, k, timeBound, dataGenerator, visualize, resultSave, solver, logic)
    #                     p = multiprocessing.Process(target=self.module, args=(
    #                         title, stlMC, formula, k, timeBound, dataGenerator, visualize, resultSave, solver, logic,
    #                         delta,
    #                         onlySTL, goals[i]))
    #                     p.start()
    #
    #                 else:
    #                     result.append(self.module(title, stlMC, formula, k, timeBound, dataGenerator, visualize, resultSave,
    #                                       solver,
    #                                       logic, delta, onlySTL, goals[i]))
    #             if not isNormal:
    #                 break
    #             if resultSave and self.is_print:
    #                 print("New filename: ./reports/" + str(filename))
    #         return result
    #     else:
    #         print("does not support trigonometric function without dreal4!")
    #         return None

















    # def parse(self):
    #     self.args = self.parser.parse_args()

    def run(self, file_name, is_visualize):
        model, PD, goals = ObjectFactory(file_name).generate_object()
        model_const = model.make_consts(1)
        solver = SolverFactory("hylaa").generate_solver()
        for goal in goals:
            goal_const = goal.make_consts(1, 60, 0, model, PD)
            result, size = solver.solve(And([model_const, goal_const]), model.range_dict)

            if is_visualize:
                integrals_list = model.get_flow_for_assignment(1)
                assignment = solver.make_assignment()
                print(assignment.get_assignments())
            # print(result)

        return model

    # def run(self, modelList=None):
    #     args = self.args
    #     save = False
    #     lower = 1
    #     upper = 1
    #     solver = 'z3'
    #     logic = 'None'
    #     stlmcPyPath = os.path.dirname(os.path.realpath(stlmcPy.__file__))
    #     visualize = False
    #     multithread = False
    #     timebound = 60
    #     step = 1
    #     onlySTL = False
    #     delta = 0
    #     if modelList is None:
    #         modelList = list()
    #     if args is not None:
    #         try:
    #             if os.path.isdir(args.file):
    #                 fileList = os.listdir(args.file)
    #                 for item in fileList:
    #                     if os.path.splitext(item)[-1].lower() == ".objects":
    #                         modelList.append(os.path.abspath(args.file) + "/" + item)
    #             elif os.path.isfile(args.file):
    #                 modelList.append(args.file)
    #             else:
    #                 raise Exception("file name is wrong")
    #             save = False if args.log is None else args.log
    #             lower = 1 if args.lower is None else args.lower
    #             upper = lower if args.upper is None else args.upper
    #             solver = 'z3' if args.solver is None else (
    #                 args.solver.lower() if args.solver.lower() in ['hylaa', 'yices', z3] else 'z3')
    #             logic = 'None'
    #             stlmcPyPath = os.path.dirname(os.path.realpath(stlmcPy.__file__))
    #             if args.logic == 'linear':
    #                 logic = 'LRA' if solver == 'z3' else 'qf_lra'
    #             elif args.logic == 'nonlinear':
    #                 logic = 'NRA' if solver == 'z3' else 'qf_nra'
    #             visualize = False if args.visualize is None else args.visualize
    #             multithread = False if args.multithread is None else args.multithread
    #             timebound = 60 if args.timebound is None else args.timebound
    #             step = 1 if args.step is None else args.step
    #             onlySTL = False if args.onlySTL is None else args.onlySTL
    #             delta = 0 if args.delta is None else args.delta
    #         except Exception as ex:
    #             if args.visualize:
    #                 if not all(argi is None for argi in
    #                            [args.lower, args.upper, args.step, args.multithread, args.timebound, args.log,
    #                             args.visualize,
    #                             args.solver, args.logic]):
    #                     print("\nNeed to provide file name!")
    #                     print("Type [-h] to see help.")
    #                     raise
    #                 try:
    #                     if not (os.path.isdir("./DataDir")):
    #                         os.makedirs(os.path.join("./DataDir"))
    #                 except OSError as e:
    #                     if e.errno != errno.EEXIST:
    #                         print("Failed to create directory!!!!!")
    #                         raise
    #                 subprocess.call([stlmcPyPath + "/visualize/main", "-v", "-webdir=" + stlmcPyPath + "/visualize/web"])
    #             else:
    #                 exc_type, exc_value, exc_traceback = sys.exc_info()
    #                 traceback.print_tb(exc_traceback, file=sys.stdout)
    #                 print(repr(ex))
    #                 print(ex)
    #
    #     # create data directory for storing report files
    #     if save:
    #         if not os.path.exists(str(os.path.abspath(os.curdir)) + "/reports/"):
    #             os.makedirs(str(os.path.abspath(os.curdir)) + "/reports/")
    #     params = dict()
    #     params["lower_bound"] = lower
    #     params["upper_bound"] = upper
    #     params["step"] = step
    #     params["time_bound"] = timebound
    #     params["is_visualize"] = visualize
    #     params["is_multithread"] = multithread
    #     params["is_save"] = save
    #     params["solver_type"] = solver.lower()
    #     params["logic_type"] = logic.upper()
    #     params["delta"] = delta
    #     params["only_stl"] = onlySTL
    #     for m in modelList:
    #         params["model_name"] = m
    #
    #     return self.modelCheck(params)
