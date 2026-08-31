from ..objects.goal import GoalFactory, OldGoalFactory
from ..objects.model import EmptyModel
from ..parser.model_visitor import ModelVisitor


def build_goals(raw_goals, labeled_factory=GoalFactory):
    """Build each parsed goal group exactly once."""
    labeled_goals, unlabeled_goals, reach_goals = raw_goals
    goals = [
        labeled_factory(raw_goal, True).generate_goal()
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


# generate only new stl encoded goal
class NewStlObjectManager(ObjectManager):
    def generate_objects(self, file_name: str):
        _, _, raw_goals, goal_labels = ModelVisitor().get_parse_tree(file_name)
        goals = build_goals(raw_goals)
        return EmptyModel(), {}, goals, goal_labels


# generate only old stl encoded goal
class OldStlObjectManager(ObjectManager):
    def generate_objects(self, file_name: str):
        _, _, raw_goals, goal_labels = ModelVisitor().get_parse_tree(file_name)
        goals = build_goals(raw_goals, OldGoalFactory)
        return EmptyModel(), {}, goals, goal_labels


class OldObjectManager:
    def generate_objects(self, file_name: str):
        model, original_prop_dict, raw_goals, goal_labels = ModelVisitor().get_parse_tree(file_name)
        goals = build_goals(raw_goals, OldGoalFactory)
        return model, original_prop_dict, goals, goal_labels


class ObjectFactory:
    _manager_types = {
        "model-with-goal": OldObjectManager,
        "only-goal-stl": OldStlObjectManager,
        "model-with-goal-enhanced": ObjectManager,
        "only-goal-stl-enhanced": NewStlObjectManager,
    }

    def __init__(self, formula_encoding: str):
        self._formula_encoding = formula_encoding

    def generate_object_manager(self):
        manager_type = self._manager_types.get(self._formula_encoding)
        if manager_type is None:
            raise ValueError(
                "unknown formula encoding {!r}; expected one of {}".format(
                    self._formula_encoding,
                    ", ".join(sorted(self._manager_types)),
                )
            )
        return manager_type()
