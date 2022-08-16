import abc

from .configuration import Configuration
from ..encoding.smt.goal.stl import StlGoal, ReachStlGoal
from ..encoding.smt.model.stlmc_model import STLmcModel
from ..parser.model_visitor import ModelVisitor


class ObjectFactory:
    def __init__(self, config: Configuration):
        self._config = config

    def generate_objects(self, file_name: str):
        cfg = self._config
        common_section = cfg.get_section("common")
        # enc = common_section.get_value("encoding")
        enc = "smt"

        if enc == "smt":
            return generate_smt_objects(file_name, cfg)
        elif enc == "automata":
            return generate_ha_objects(file_name)
        else:
            raise Exception("not supported encoding type {}".format(enc))


def generate_smt_objects(file_name: str, config: Configuration):
    raw_model, prop_dict, raw_goals, goal_labels = ModelVisitor().get_parse_tree(file_name)
    (labeled_goals, unlabeled_goals, reach_goals) = raw_goals

    common_section = config.get_section("common")
    threshold = float(common_section.get_value("threshold"))
    tb = float(common_section.get_value("time-bound"))

    cfg = dict()
    cfg["prop_dict"] = prop_dict
    cfg["threshold"] = threshold
    cfg["time-bound"] = tb

    goals = list()
    for raw_goal in labeled_goals:
        goals.append(StlGoal(raw_goal, cfg))

    for raw_goal in unlabeled_goals:
        goals.append(StlGoal(raw_goal, cfg))

    for raw_goal in reach_goals:
        goals.append(ReachStlGoal(raw_goal))

    return STLmcModel(*raw_model, threshold), prop_dict, goals, goal_labels


def generate_ha_objects(file_name: str):
    return None
