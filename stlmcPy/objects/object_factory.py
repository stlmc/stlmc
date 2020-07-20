from stlmcPy.objects.goal import GoalFactory
from stlmcPy.parser.model_visitor import ModelVisitor


class ObjectFactory:
    def __init__(self, file_name: str):
        self.file_name = file_name

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
