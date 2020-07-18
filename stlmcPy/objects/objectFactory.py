from functools import singledispatch

from stlmcPy.constraints.constraints import *
from stlmcPy.objects.goal import GoalFactory
from stlmcPy.parser.model_visitor import ModelVisitor


class ObjectFactory:
    def __init__(self, file_name: str):
        self.file_name = file_name
        # self.counter = 0
        # self.proposition_dict = dict()
        # self.new_var_prefix = "newPropDecl_"

    # @singledispatch
    # def transform_goal_condition(self, formula: Formula):
    #     return formula
    #
    # @transform_goal_condition.register(UntilFormula)
    # def _(self, formula: UntilFormula):
    #     left = self.transform_goal_condition(formula.left)
    #     right = self.transform_goal_condition(formula.right)
    #     return UntilFormula(formula.local_time, formula.global_time, left, right)
    #
    # @transform_goal_condition.register(FinallyFormula)
    # def _(self, formula: FinallyFormula):
    #     return FinallyFormula(formula.local_time, formula.global_time, self.transform_goal_condition(formula.child))
    #
    # @transform_goal_condition.register(GloballyFormula)
    # def _(self, formula: GloballyFormula):
    #     return GloballyFormula(formula.local_time, formula.global_time, self.transform_goal_condition(formula.child))
    #
    # @transform_goal_condition.register(ReleaseFormula)
    # def _(self, formula: ReleaseFormula):
    #     left = self.transform_goal_condition(formula.left)
    #     right = self.transform_goal_condition(formula.right)
    #     return ReleaseFormula(formula.local_time, formula.global_time, left, right)
    #
    # @transform_goal_condition.register(And, Or, Not, Gt, Geq, Lt, Leq, Neq, Eq, Implies)
    # def _(self, formula: And):
    #     new_var_str = self.new_var_prefix + str(self.counter)
    #     new_var = Bool(new_var_str)
    #     self.proposition_dict[new_var] = formula
    #     self.counter += 1
    #     return new_var

    # @transform_goal_condition.register(Or)
    # def _(self, formula: Or):
    #     return formula
    #
    # @transform_goal_condition.register(Not)
    # def _(self, formula: Not):
    #     return formula
    #
    # @transform_goal_condition.register(Gt)
    # def _(self, formula: Gt):
    #     return formula
    #
    # @transform_goal_condition.register(Geq)
    # def _(self, formula: Geq):
    #     return formula
    #
    # @transform_goal_condition.register(Lt)
    # def _(self, formula: Lt):
    #     return formula
    #
    # @transform_goal_condition.register(Leq)
    # def _(self, formula: And):
    #     return formula
    #
    # @transform_goal_condition.register(Implies)
    # def _(self, formula: Implies):
    #     return formula
    #
    # @transform_goal_condition.register(Eq)
    # def _(self, formula: Eq):
    #     return formula
    #
    # @transform_goal_condition.register(Neq)
    # def _(self, formula: Neq):
    #     return formula

    def generate_object(self):
        model, original_prop_dict, raw_goals = ModelVisitor().get_parse_tree(self.file_name)
        goals = list()
        new_prop_dict = original_prop_dict.copy()
        goal_variable_index = 0
        for raw_goal in raw_goals:
            # TODO: Performance Issue maybe...
            # get transformed raw_goal and its mapping info as dictionary
            goals.append(GoalFactory(raw_goal).generate_goal())
            # new_goal, goal_prop_dict = self.transform_goal_condition(raw_goal, goal_variable_index)
        #     new_prop_dict.add_info(goal_prop_dict)
        #     # generate Goal class with this new_goal
        #     goals.append(GoalFactory(new_goal).generate_goal())
        #     goal_variable_index += len(goal_prop_dict)
        print(goals)
        # return model, new_prop_dict, goals
        return model, original_prop_dict, goals
