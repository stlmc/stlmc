from typing import Callable, Iterable


def until_robustness(
        witness_times: Iterable[float],
        prefix_times: Callable[[float], Iterable[float]],
        left_value: Callable[[float], float],
        right_value: Callable[[float], float]) -> float:
    """Discrete-sample robustness of ``left U right``."""
    return max(
        min(
            right_value(witness),
            min(left_value(t) for t in prefix_times(witness)),
        )
        for witness in witness_times
    )


def release_robustness(
        witness_times: Iterable[float],
        prefix_times: Callable[[float], Iterable[float]],
        left_value: Callable[[float], float],
        right_value: Callable[[float], float]) -> float:
    """Discrete-sample robustness of ``left R right``."""
    return min(
        max(
            right_value(witness),
            max(left_value(t) for t in prefix_times(witness)),
        )
        for witness in witness_times
    )
