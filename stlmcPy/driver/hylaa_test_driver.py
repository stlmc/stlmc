from stlmcPy.constraints.constraints import And
from stlmcPy.driver.base_driver import DriverFactory, StlConfiguration, Runner
from stlmcPy.objects.object_builder import generate_object
from stlmcPy.solver.solver_factory import SolverFactory


class HylaaTestRunner(Runner):
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


class HylaaTestDriverFactory(DriverFactory):
    def __init__(self):
        super().__init__()

    def make_config(self):
        return StlConfiguration()

    def make_runner(self):
        return Runner()
