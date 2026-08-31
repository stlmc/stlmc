"""Application-level orchestration contracts."""

from .result import VerificationOutcome, interpret_algorithm_result

__all__ = ["VerificationOutcome", "interpret_algorithm_result"]
