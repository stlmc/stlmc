"""Scoped bookkeeping shared by assumption-based exact solver adapters."""

from .abstract_solver import IncrementalFormulaSolver, SolverStatus
from ..constraints.analysis import get_vars
from ..utils.interrupt import raise_if_interrupted


class AssumptionFormulaSolver(IncrementalFormulaSolver):
    """Native hooks use private guard terms, never user-visible symbols.

    Track IDs must be unique while active. A fork is an independent, flat
    snapshot of all active ordinary and tracked assertions, without scopes.
    """

    def _init_state(self, logic):
        self.logic = logic
        self._assertions = []
        self._tracked = {}
        self._tracked_terms = {}
        self._scopes = []
        self._status = None

    def add(self, formula):
        raise_if_interrupted()
        self._assert(self._term(formula))
        self._assertions.append(formula)
        self._status = None

    def push(self):
        raise_if_interrupted()
        self._push()
        self._scopes.append((len(self._assertions), set(self._tracked)))
        self._status = None

    def pop(self):
        raise_if_interrupted()
        size, ids = self._scopes[-1]
        self._pop()
        self._scopes.pop()
        del self._assertions[size:]
        self._tracked = {k: v for k, v in self._tracked.items() if k in ids}
        self._tracked_terms = {k: v for k, v in self._tracked_terms.items() if k in ids}
        self._status = None

    def track(self, formula, track_id):
        raise_if_interrupted()
        if track_id in self._tracked:
            raise ValueError("duplicate active track ID: {}".format(track_id))
        guard = self._guard(self._term(formula))
        self._tracked[track_id] = formula
        self._tracked_terms[track_id] = guard
        self._status = None

    def check(self):
        raise_if_interrupted()
        self._status = None
        self._status = self._check(list(self._tracked_terms.values()))
        raise_if_interrupted()
        return self._status

    def unsat_core(self):
        if self._status != SolverStatus.UNSAT:
            raise ValueError("unsat_core requires an UNSAT check")
        reverse = {term: key for key, term in self._tracked_terms.items()}
        return {reverse[term] for term in self._core()}

    def _active_variables(self):
        variables = set()
        for formula in self._assertions + list(self._tracked.values()):
            variables.update(get_vars(formula))
        return variables

    def _require_model(self):
        if self._status != SolverStatus.SAT:
            raise ValueError("model requires a SAT check")

    def fork(self):
        result = type(self)(self.logic)
        for formula in self._assertions:
            result.add(formula)
        for track_id, formula in self._tracked.items():
            result.track(formula, track_id)
        return result
