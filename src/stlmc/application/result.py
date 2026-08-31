from dataclasses import dataclass


@dataclass(frozen=True)
class VerificationOutcome:
    """User-facing meaning of an algorithm's legacy three-valued result."""

    status: str
    has_witness: bool


def interpret_algorithm_result(result: str, reachability: bool):
    if reachability:
        statuses = {
            "False": "unreachable",
            "True": "reachable",
            "Unknown": "unknown",
        }
        witness_result = "True"
    else:
        statuses = {
            "False": "violated",
            "True": "satisfied",
            "Unknown": "unknown",
        }
        witness_result = "False"
    return VerificationOutcome(
        statuses.get(result, "unknown"), result == witness_result
    )
