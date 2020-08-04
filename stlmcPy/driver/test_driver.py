from stlmcPy.driver.driver import Driver
from stlmcPy.objects.object_factory import ObjectFactory
from stlmcPy.DataGenerator import *
from stlmcPy.solver.solver_factory import SolverFactory
from stlmcPy.visualize.visualizer import Visualizer


class TestDriver(Driver):
    def __init__(self):
        super(TestDriver, self).__init__()

    def run(self, file_name, is_visualize):
        model, PD, goals = ObjectFactory(file_name).generate_object()
        model_const = model.make_consts(1)
        solver = SolverFactory("hylaa").generate_solver()
        # visualizer = Visualizer()
        for goal in goals:
            goal_const = goal.make_consts(1, 60, 0, model, PD)
            result, size = solver.solve(And([model_const, goal_const]), model.range_dict)
            print("Driver: solver returns " + str(result))
            if result is False:
                assignment = solver.make_assignment()
                assn = assignment.get_assignments()
                # visualizer.run(assn, model.modules, model.mode_var_dict, model.range_dict, PD)

        return model
