# from stlmcPy.driver.driver import Driver
# from stlmcPy.objects.object_factory import generate_object
# from stlmcPy.DataGenerator import *
#
# from stlmcPy.driver.base_driver import StlConfiguration
# from stlmcPy.solver.solver_factory import SolverFactory
#
#
# class TestDriver(Driver):
#     def __init__(self):
#         super(TestDriver, self).__init__()
#
#     def run(self, file_name, is_visualize):
#         model, PD, goals = generate_object()
#         model_const = model.make_consts(1)
#         solver = SolverFactory("hylaa").generate_solver()
#         # visualizer = Visualizer()
#         for goal in goals:
#             goal_const = goal.make_consts(1, 60, 0, model, PD)
#             result, size = solver.solve(And([model_const, goal_const]), model.range_dict)
#             print("Driver: solver returns " + str(result))
#             if result is False:
#                 assignment = solver.make_assignment()
#                 assn = assignment.get_assignments()
#                 # visualizer.run(assn, model.modules, model.mode_var_dict, model.range_dict, PD)
#
#         return model
#
#
# class Runner:
#     def run(self, config: StlConfiguration):
#         model, PD, goals = generate_object(config.file_name)
#         model_const = model.make_consts(1)
#         solver = SolverFactory("hylaa").generate_solver()
#         for goal in goals:
#             goal_const = goal.make_consts(1, 60, 0, model, PD)
#             result, size = solver.solve(And([model_const, goal_const]), model.range_dict)
#             # if is_visualize:
#             # integrals_list = model.get_flow_for_assignment(1)
#             # assignment = solver.make_assignment()
#             # print(assignment.get_assignments())
#             # print(result)
#
#         return model
#
#
# class DriverFactory:
#     def __init__(self):
#         pass
#
#     @abc.abstractmethod
#     def make_config(self):
#         return StlConfiguration()
#
#     @abc.abstractmethod
#     def make_runner(self):
#         return Runner()
