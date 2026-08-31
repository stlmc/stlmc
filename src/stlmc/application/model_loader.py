from ..objects.goal import GoalFactory
from ..parser.model_visitor import ModelVisitor


def build_goals(raw_goals):
    """Build each parsed goal group exactly once."""
    labeled_goals, unlabeled_goals, reach_goals = raw_goals
    goals = [
        GoalFactory(raw_goal, True).generate_goal()
        for raw_goal in labeled_goals
    ]
    goals.extend(
        GoalFactory(raw_goal, True).generate_goal()
        for raw_goal in unlabeled_goals
    )
    goals.extend(
        GoalFactory(raw_goal, True).generate_goal(is_reach=True)
        for raw_goal in reach_goals
    )
    return goals


class ObjectManager:
    def generate_objects(self, file_name: str):
        model, original_prop_dict, raw_goals, goal_labels = ModelVisitor().get_parse_tree(file_name)
        goals = build_goals(raw_goals)
        return model, original_prop_dict, goals, goal_labels
