"""Typed application options derived from the parser's configuration model."""

from dataclasses import dataclass, replace
from typing import Tuple

from ..config_schema import resolve_parallel_core
from ..exceptions import IllegalArgumentError, NotSupportedError


@dataclass(frozen=True)
class RunOptions:
    solver: str
    bound: int
    time_bound: float
    time_horizon: float
    threshold: float
    parallel_core: int
    solver_batch_size: int
    path_strategy: str
    goal_labels: Tuple[str, ...]
    two_step: bool
    concrete: bool
    parallel: bool
    visualize: bool
    verbose: bool
    reach: bool
    smt_preprocess: bool

    @classmethod
    def from_configuration(cls, configuration):
        common = configuration.get_section("common")
        raw_horizon = common.get_value("time-horizon")
        raw_time_bound = common.get_value("time-bound")
        horizon = raw_time_bound if raw_horizon == "time-bound" else raw_horizon
        raw_labels = (
            common.get_value("goal") if common.is_argument_in("goal") else "all"
        )
        labels = tuple(label.strip() for label in raw_labels.split(","))
        if "all" in labels:
            if len(labels) != 1:
                raise NotSupportedError(
                    '"all" cannot be combined with other goal labels'
                )
            labels = ()

        parallel_core = int(resolve_parallel_core(common.get_value("parallel-core")))
        batch_size = int(common.get_value("solver-batch-size"))
        if batch_size < 1:
            raise IllegalArgumentError("solver-batch-size must be at least 1")
        if parallel_core < 1:
            raise IllegalArgumentError("parallel-core must be at least 1")

        enabled = lambda name: common.get_value(name) == "true"
        return cls(
            solver=common.get_value("solver"),
            bound=int(common.get_value("bound")),
            time_bound=float(raw_time_bound),
            time_horizon=float(horizon),
            threshold=float(common.get_value("threshold")),
            parallel_core=parallel_core,
            solver_batch_size=batch_size,
            path_strategy=common.get_value("path-strategy"),
            goal_labels=labels,
            two_step=enabled("two-step"),
            concrete=enabled("concrete"),
            parallel=enabled("parallel"),
            visualize=enabled("visualize"),
            verbose=enabled("verbose"),
            reach=enabled("reach"),
            smt_preprocess=enabled("smt-preprocess"),
        )

    def with_solver(self, solver):
        return replace(self, solver=solver)

    @property
    def algorithm_name(self):
        return "two-step" if self.two_step else "one-step"
