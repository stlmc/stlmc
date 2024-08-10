from functools import singledispatch

from ..constraints.constraints import *
from ..solver.abstract_solver import BaseSolver
from ..solver.strategy import unit_split
from ..solver.z3 import Z3Solver
from ..strategy.core import Generator, SmtNode
from ..util.logger import Logger


class SsmtSolver(BaseSolver):
    def solve(self, all_consts=None, cont_vars_dict=None, boolean_abstract_dict=None):
        assert len(all_consts.children) == 3 and all_consts is not None

        model_const, goal_const, boolean_abstract_consts = all_consts.children
        # print(model_const)
        # k = 1

        generator = Generator(model_const.children)
        # for k in generator.bound_info:
        #     print("{} ==> {}".format(k, generator.bound_info[k]))

        # generator.dfs(generator.first_node)
        n, ii = generator.next(generator.first_node, 0)
        print("n : {}, ii : {}".format(generator.first_node, 0))
        n2, ii2 = generator.next(n, ii)
        print("n1 : {}, ii2 : {}".format(n, ii))
        # zero = generator.next(generator.first_node, 0)

        # first = generator.next(zero, 0)

        # print("zero : \n{}\n".format(zero))
        # print("first : \n{}\n".format(first))
        # print(init)

        # if result is False:
        #     print("assignment exists")
        #     assignment = z3solver.make_assignment()
        #     print(assignment.get_assignments())
        # print(result)

        # assert init is not None
        # print(goal_const)

        logger = self.logger
        logger.start_timer("solving timer")
        # print(model_const)
        logger.stop_timer("solving timer")
        self.set_time("solving timer", logger.get_duration_time("solving timer"))
        return "False", 0

    def make_assignment(self):
        pass

    def clear(self):
        pass
