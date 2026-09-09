from dataclasses import dataclass
from enum import Enum
from typing import Iterator


class SearchStatus(Enum):
    """Meaning of a bounded search, independent of the property kind."""

    WITNESS_FOUND = "witness-found"
    EXHAUSTED = "exhausted"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class AlgorithmResult:
    """Typed result returned by model-checking algorithms.

    Iteration is retained temporarily so third-party callers which unpacked the
    former four-tuple continue to work while migrating to named attributes.
    """

    status: SearchStatus
    elapsed: float
    finished_bound: int
    assignment: object = None
    legacy_status: str = None

    def __iter__(self) -> Iterator[object]:
        yield self.legacy_status if self.legacy_status is not None else self.status
        yield self.elapsed
        yield self.finished_bound
        yield self.assignment

    def __len__(self):
        return 4

    def __getitem__(self, index):
        return tuple(iter(self))[index]


@dataclass(frozen=True)
class VerificationOutcome:
    """User-facing meaning of an algorithm's legacy three-valued result."""

    status: str
    has_witness: bool


def interpret_algorithm_result(result, reachability: bool):
    """Translate a search result into the terminology shown to users.

    The string branch is a compatibility boundary for integrations using the
    pre-1.1 truth-valued algorithm contract.
    """
    if isinstance(result, AlgorithmResult):
        result = result.status
    if isinstance(result, SearchStatus):
        if result is SearchStatus.UNKNOWN:
            return VerificationOutcome("unknown", False)
        if result is SearchStatus.WITNESS_FOUND:
            return VerificationOutcome(
                "reachable" if reachability else "violated", True
            )
        return VerificationOutcome(
            "unreachable" if reachability else "satisfied", False
        )

    if reachability:
        statuses = {"False": "unreachable", "True": "reachable", "Unknown": "unknown"}
        witness_result = "True"
    else:
        statuses = {"False": "violated", "True": "satisfied", "Unknown": "unknown"}
        witness_result = "False"
    return VerificationOutcome(statuses.get(result, "unknown"), result == witness_result)
