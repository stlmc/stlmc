from stlmcPy.objects.goal import GoalFactory
from stlmcPy.parser.model_visitor import ModelVisitor


def generate_object(file_name: str):
    model, original_prop_dict, raw_goals = ModelVisitor().get_parse_tree(file_name)
    goals = list()
    for raw_goal in raw_goals:
        goals.append(GoalFactory(raw_goal).generate_goal())
    return model, original_prop_dict, goals

