import abc

from stlmcPy.objects.goal import GoalFactory, OldGoalFactory
from stlmcPy.objects.model import EmptyModel
from stlmcPy.parser.model_visitor import ModelVisitor


class ObjectManager:
    @abc.abstractmethod
    def generate_objects(self, file_name: str):
        model, original_prop_dict, raw_goals = ModelVisitor().get_parse_tree(file_name)
        goals = list()
        for raw_goal in raw_goals:
            goals.append(GoalFactory(raw_goal).generate_goal())
        return model, original_prop_dict, goals


# generate only new stl encoded goal
class NewStlObjectManager(ObjectManager):
    def generate_objects(self, file_name: str):
        _, _, raw_goals = ModelVisitor().get_parse_tree(file_name)
        goals = list()
        for raw_goal in raw_goals:
            goals.append(GoalFactory(raw_goal).generate_goal())
        return EmptyModel(), {}, goals


# generate only old stl encoded goal
class OldStlObjectManager(ObjectManager):
    def generate_objects(self, file_name: str):
        _, _, raw_goals = ModelVisitor().get_parse_tree(file_name)
        goals = list()
        for raw_goal in raw_goals:
            goals.append(OldGoalFactory(raw_goal).generate_goal())
        return EmptyModel(), {}, goals


class ObjectFactory:
    def __init__(self, formula_encoding: str):
        self._formula_encoding = formula_encoding

    def generate_object_manager(self):
        if self._formula_encoding == "model-with-goal":
            return ObjectManager()
        elif self._formula_encoding == "only-goal-stl":
            return OldStlObjectManager()
        elif self._formula_encoding == "only-goal-stl-enhanced":
            return NewStlObjectManager()
