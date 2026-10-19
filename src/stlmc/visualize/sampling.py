"""Time, discrete-state, and continuous-solution sampling utilities."""

import abc
from typing import Dict, List

import numpy as np
from scipy.integrate import odeint

from ..constraints.constraints import Bool, Dynamics, Int, Real, Variable
from .numeric import infix_float
from .numbers import number_float


def sample_max(time_list: List[List[float]]):
    return max(
        (time for interval in time_list for time in interval),
        default=-1,
    )


def get_sub_time_samples(time_sample_list: List[List[float]], start: float,
                         end: float, time_max: float) -> List[float]:
    """Return bounded witness samples without synthesizing the horizon."""
    if start >= time_max or end < start:
        return []
    times = [time for interval in time_sample_list for time in interval]
    return [time for time in times if start <= time <= end and time < time_max]


class TimeSampler:
    def __init__(self, projector):
        self.projector = projector

    def generate_samples(self, endpoint=True) -> List[List[float]]:
        arrays = []
        variable_points = self.projector.get_variable_points()
        assignment = self.projector.assignment
        for index in range(len(variable_points) - 1):
            current = number_float(assignment[variable_points[index]].value)
            following = number_float(
                assignment[variable_points[index + 1]].value
            )
            arrays.append(np.linspace(
                current, following,
                endpoint=endpoint,
            ))
        return [[value.item() for value in array] for array in arrays]


class DiscreteSampler:
    def __init__(self, projector):
        self.projector = projector

    def generate_samples_at(self, time_samples: List[float], bound):
        assignment = self.projector.assignment
        type_dict = {"real": Real, "bool": Bool, "int": Int}
        result: Dict[Variable, List[float]] = {}
        for variable in self.projector.get_mode_vars():
            variable_type = variable.type
            bound_variable = type_dict[variable_type](
                "{}_{}".format(variable.id, bound)
            )
            # dReal's numeric model entries are decoded as Real intervals,
            # including declared integer modes. Use the model's explicit
            # mode type for sampling, without changing the assignment or
            # coercing Boolean/continuous variables. Other backends' typed
            # integer entries take precedence when both keys are present.
            if variable_type == "int" and bound_variable not in assignment:
                bound_variable = Real(bound_variable.id)
            if bound_variable not in assignment:
                continue
            assigned = assignment[bound_variable]
            if variable_type == "bool":
                value = 1 if assigned.value == "True" else -1
            else:
                value = number_float(assigned.value)
            result[variable] = [value for _ in time_samples]
        return result


class PointSampler:
    @abc.abstractmethod
    def generate_samples(self, time_samples: List[float], dynamic: Dynamics,
                         initial_values: List[float]):
        pass


class SolutionPointSampler(PointSampler):
    def generate_samples(self, time_samples: List[float], dynamic: Dynamics,
                         initial_values: List[float]):
        normalized_times = [time - time_samples[0] for time in time_samples]
        variables = list(dynamic.vars) + [Real("time")]
        values = list(initial_values) + [0.0]
        result = {}
        for index, variable in enumerate(dynamic.vars):
            expression = dynamic.exps[index]
            samples = []
            for time in normalized_times:
                values[-1] = time
                samples.append(float(infix_float(expression, values, variables)))
            result[variable] = samples
        return result


class OdePointSampler(PointSampler):
    def generate_samples(self, time_samples: List[float], dynamic: Dynamics,
                         initial_values: List[float]):
        values = odeint(
            lambda state, _: [
                infix_float(expression, state, dynamic.vars)
                for expression in dynamic.exps
            ],
            initial_values,
            time_samples,
        )
        return {
            variable: [sample[index] for sample in values]
            for index, variable in enumerate(dynamic.vars)
        }


__all__ = [
    "DiscreteSampler", "OdePointSampler", "PointSampler",
    "SolutionPointSampler", "TimeSampler", "get_sub_time_samples",
    "sample_max",
]
