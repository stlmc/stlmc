"""Application-level orchestration contracts."""

from .result import (
    AlgorithmResult, SearchStatus, VerificationOutcome,
    interpret_algorithm_result,
)

__all__ = [
    "AlgorithmResult", "SearchStatus", "VerificationOutcome",
    "interpret_algorithm_result",
]
