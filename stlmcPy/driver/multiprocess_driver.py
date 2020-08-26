from stlmcPy.constraints.constraints import And
from stlmcPy.constraints.operations import make_boolean_abstract_consts
from stlmcPy.driver.base_driver import DriverFactory, StlConfiguration, Runner, StlModelChecker
from stlmcPy.objects.object_builder import generate_object
from stlmcPy.solver.solver_factory import SolverFactory

from timeit import default_timer as timer


def unit_run(arg):
    mul_runner, cur_bound, file_name, solver, model, goal, PD = arg
    print(file_name)
    if cur_bound == 1:
        mul_runner.write_to_file(file_name + ".csv")
    print(file_name)
    solver.add_bound(cur_bound)
    model_const = model.make_consts(cur_bound)
    goal_const, goal_boolean_abstract = goal.make_consts(cur_bound, 60, 1, model, PD)

    boolean_abstract = dict()
    boolean_abstract.update(model.boolean_abstract)
    boolean_abstract.update(goal_boolean_abstract)
    boolean_abstract_consts = make_boolean_abstract_consts(boolean_abstract)

    solve_start = timer()
    result, size = solver.solve(And([model_const, goal_const, boolean_abstract_consts]),
                                model.range_dict, boolean_abstract)

    solve_end = timer()
    mul_runner.concat(solver.get_total_log())
    solver.clear_log()
    print("Driver returns : " + str(result) + ", Total solving time : " + str(solve_end - solve_start))
    mul_runner.add_result(result)
    mul_runner.add_total_time(str(solve_end - solve_start))
    mul_runner.add_log_info()
    model.clear()
    goal.clear()
    print("======================================")
    mul_runner.append_to_file(file_name + ".csv")
    mul_runner.clear_log()


class MultiprocessRunner(Runner):
    def __init__(self):
        super().__init__()
        self.jobs = []
        self.arguments = []

    def run(self, config: StlConfiguration):
        for file_name in config.file_list:
            model, PD, goals = generate_object(file_name)
            for bound in config.bound:
                for goal in goals:
                    new_file_name = str(file_name) + "_###" + str(goal.get_formula()) + "_###" + config.solver + "_" + str(
                        bound)
                    solver = SolverFactory(config.solver).generate_solver()
                    arg = self, bound, new_file_name, solver, model, goal, PD
                    self.arguments.append(arg)
        print("multiprocess arguments: {}".format(str(len(self.arguments))))


class MultiprocessDriverFactory(DriverFactory):
    def __init__(self):
        super().__init__()

    def make_config(self):
        return StlConfiguration()

    def make_runner(self):
        return MultiprocessRunner()


class MultiprocessStlModelChecker(StlModelChecker):
    def __init__(self):
        super().__init__()

    def get_args(self):
        return self.runner.arguments
