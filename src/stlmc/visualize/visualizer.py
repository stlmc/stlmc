import errno
import os
from typing import List, Dict, Set, Tuple

from ..constraints.constraints import Constraint, Formula, Ode, Variable
from ..constraints.substitution import substitution
from ..artifacts.formula_index import index_subformulas as sub_formula
from ..exceptions import NotSupportedError
from .latex import formula2latex, interval_string
from .grouping import flatten, pairwise_disjoint_check, split_groups
from .projection import Projector, continuous_values
from .robustness import robustness
from .text_output import write_counterexample_text
from .sampling import (
    DiscreteSampler, OdePointSampler, PointSampler, SolutionPointSampler,
    TimeSampler, get_sub_time_samples, sample_max,
)


class Visualizer:
    def __init__(self):
        self.assignment = dict()
        self.visualize_dict = dict()
        self.plot = None

    def write(self, file_name):
        if self.plot is None:
            raise NotSupportedError("plot must not be none!")
        from .plotting import require_bokeh
        require_bokeh()
        from bokeh.io import output_file, save
        output_file(filename="{}.html".format(file_name))
        save(self.plot)
        self.plot = None
        print("write counterexample graphs: \'{}.html\'".format(file_name))

    def write_text(self, file_name, assignment: dict, modules: dict,
                   mode_var_dict: Dict[str, Variable],
                   propositions: Dict[Variable, Constraint], cont_var_dict: dict,
                   prop_dict: dict, formula: Constraint, formula_label: str,
                   delta: float, init=None, const_dict=None):
        return write_counterexample_text(
            file_name, assignment, modules, mode_var_dict, propositions,
            cont_var_dict, prop_dict, formula, formula_label, delta,
            init, const_dict,
        )

    def generate_data(self, assignment: dict, modules: dict, mode_var_dict: Dict[str, Variable],
                      propositions: Dict[Variable, Constraint], cont_var_dict: dict, prop_dict: dict,
                      formula: Constraint, formula_label: str, delta: float):
        self.assignment.clear()
        ff = substitution(formula, prop_dict)
        subformulas, formula_id_dict = sub_formula(ff)

        projector = Projector(assignment, mode_var_dict, propositions, modules)

        max_bound = projector.get_max_bound()
        time_sampler = TimeSampler(projector)
        time_samples_list = time_sampler.generate_samples()
        time_max = sample_max(time_samples_list)

        ordered_modules = projector.get_ordered_modules()
        c_val = self.make_cont_values(assignment, cont_var_dict, max_bound)

        point_samples: Dict[Variable, List[List[float]]] = dict()
        discrete_samples: Dict[Variable, List[List[float]]] = dict()

        op = OdePointSampler()
        sp = SolutionPointSampler()
        ds = DiscreteSampler(projector)

        for interval_index, module in enumerate(ordered_modules):
            initial_values = list()
            for v in module["flow"].vars:
                initial_values.append(c_val[v.id][interval_index][0])

            dynamics = module["flow"]
            if isinstance(dynamics, Ode):
                gen_dict = op.generate_samples(time_samples_list[interval_index], dynamics, initial_values)

            else:
                gen_dict = sp.generate_samples(time_samples_list[interval_index], dynamics, initial_values)

            for v in gen_dict:
                if v in point_samples:
                    point_samples[v].append(gen_dict[v])
                else:
                    point_samples[v] = [gen_dict[v].copy()]

            discrete_dict = ds.generate_samples_at(time_samples_list[interval_index], interval_index)
            for v in discrete_dict:
                if v in discrete_samples:
                    discrete_samples[v].append(discrete_dict[v])
                else:
                    discrete_samples[v] = [discrete_dict[v]]

        robustness_dict = dict()
        print("calculate robustness values ...")
        dp_table: Dict[Tuple[Formula, float], float] = dict()
        for f in subformulas:
            robustness_dict[f] = list()
            for time_sample in time_samples_list:
                sample_list = list()
                for time in time_sample:
                    rob = robustness(f, point_samples, discrete_samples, time, time_samples_list, time_max, dp_table)
                    sample_list.append(rob)
                robustness_dict[f].append(sample_list)

        return point_samples, robustness_dict, time_samples_list, formula_id_dict, formula_label, delta

    def generate_plot(self, assignment: dict, modules: dict, mode_var_dict: Dict[str, Variable],
                      propositions: Dict[Variable, Constraint], cont_var_dict: dict, prop_dict: dict,
                      formula: Constraint, formula_label: str, delta: float, user_defined_groups: Dict[int, Set[str]]):

        from .plotting import build_plot, require_bokeh
        require_bokeh()
        point_samples, robustness_dict, time_samples_list, formula_id_dict, _, _ = self.generate_data(assignment,
                                                                                                      modules,
                                                                                                      mode_var_dict,
                                                                                                      propositions,
                                                                                                      cont_var_dict,
                                                                                                      prop_dict,
                                                                                                      formula,
                                                                                                      formula_label,
                                                                                                      delta)
        self.plot = build_plot(
            point_samples, robustness_dict, time_samples_list,
            formula_id_dict, formula_label, delta, user_defined_groups,
        )


    @staticmethod
    def make_cont_values(assignment: dict, cont_var_dict: dict, max_bound):
        return continuous_values(assignment, cont_var_dict, max_bound)
