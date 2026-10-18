import multiprocessing
import signal
import threading
import time
from fractions import Fraction
from queue import Empty

# Some native builds crash at process teardown if the Yices binding is first
# initialized after the CVC5 extension. Fix the optional library import order;
# Yices remains optional and reports its own error only when selected.
try:
    from importlib import import_module
    import_module("yices")
except Exception:
    pass

import cvc5
from cvc5 import Kind

from ..constraints.constraints import (
    Add, And, Bool, BoolVal, Div, Eq, Forall, Geq, Gt, Implies, IntVal,
    Integral, Leq, Lt, Mul, Neg, Neq, Not, Or, Pow, Real, RealVal, Sub,
    Variable,
)
from ..constraints.analysis import get_vars, size_of_tree
from ..constraints.logical_normalization import reduce_not
from ..constraints.normalization import reverse_inequality
from ..constraints.translation import make_dynamics_consts, make_forall_consts
from ..exceptions import NotSupportedError
from ..solver.abstract_solver import JobSolver, SolveResult, SolverJob, SolverStatus
from ..solver.assignment import Assignment
from .formula_state import AssumptionFormulaSolver
from ..utils.smt2_output import is_enabled, write_smt2


class CVC5Assignment(Assignment):
    def __init__(self, assignments=None, solver=None, translator=None):
        self._assignments = assignments or {}
        self._solver = solver
        self._translator = translator

    def get_assignments(self):
        return dict(self._assignments)

    def eval(self, const):
        if self._solver is None:
            raise NotSupportedError("CVC5 has no active model")
        term = self._translator.term(const)
        return _assignment_value(term, self._solver.getValue(term))


class _CVC5Translator:
    """Translate STLmc constraints without exposing CVC5 terms upstream."""

    def __init__(self, solver):
        self.solver = solver
        self.variables = {}

    def variable(self, variable):
        if variable not in self.variables:
            sorts = {
                "bool": self.solver.getBooleanSort(),
                "int": self.solver.getIntegerSort(),
                "real": self.solver.getRealSort(),
            }
            self.variables[variable] = self.solver.mkConst(
                sorts[variable.type], variable.id
            )
        return self.variables[variable]

    def term(self, const):
        if isinstance(const, BoolVal):
            if const.value not in {"True", "False"}:
                raise NotSupportedError("CVC5 cannot translate {}".format(const))
            return self.solver.mkBoolean(const.value == "True")
        if isinstance(const, RealVal):
            return self.solver.mkReal("99999" if const.value == "inf" else const.value)
        if isinstance(const, IntVal):
            return self.solver.mkInteger("99999" if const.value == "inf" else const.value)
        if isinstance(const, Variable):
            return self.variable(const)
        if isinstance(const, Integral):
            return self.term(make_dynamics_consts(const.dynamics))
        if isinstance(const, Forall):
            return self._forall(const)
        if isinstance(const, Pow):
            try:
                exponent = int(const.right.value)
            except (AttributeError, TypeError, ValueError) as error:
                raise NotSupportedError(
                    "CVC5 requires a non-negative integer exponent"
                ) from error
            if exponent < 0:
                raise NotSupportedError(
                    "CVC5 requires a non-negative integer exponent"
                )
            base = self.term(const.left)
            if exponent == 0:
                return self.solver.mkReal(1)
            if exponent == 1:
                return base
            return self.solver.mkTerm(Kind.MULT, *([base] * exponent))
        unary = {Neg: Kind.NEG, Not: Kind.NOT}
        binary = {
            Geq: Kind.GEQ, Gt: Kind.GT, Leq: Kind.LEQ, Lt: Kind.LT,
            Eq: Kind.EQUAL, Neq: Kind.DISTINCT, Add: Kind.ADD,
            Sub: Kind.SUB, Mul: Kind.MULT, Div: Kind.DIVISION,
            Implies: Kind.IMPLIES,
        }
        multinary = {And: Kind.AND, Or: Kind.OR}
        if type(const) in unary:
            return self.solver.mkTerm(unary[type(const)], self.term(const.child))
        if type(const) in binary:
            left = self.term(const.left)
            right = self.term(const.right)
            left_sort = left.getSort()
            right_sort = right.getSort()
            # SMT-LIB arithmetic permits Int terms in a Real context, but
            # the CVC5 API requires the coercion to be explicit.
            if left_sort.isInteger() and right_sort.isReal():
                left = self.solver.mkTerm(Kind.TO_REAL, left)
            elif left_sort.isReal() and right_sort.isInteger():
                right = self.solver.mkTerm(Kind.TO_REAL, right)
            return self.solver.mkTerm(
                binary[type(const)], left, right
            )
        if type(const) in multinary:
            children = [self.term(child) for child in const.children]
            if not children:
                return self.solver.mkBoolean(True)
            if len(children) == 1:
                return children[0]
            return self.solver.mkTerm(multinary[type(const)], *children)
        raise NotSupportedError(
            "CVC5 cannot translate {}: {}".format(const, type(const))
        )

    def _forall(self, const):
        if isinstance(const.const, (Or, Implies)):
            from ..constraints.quantified_flow import flow_condition_at_time
            time = self.solver.mkVar(self.solver.getRealSort(), "stlmc_flow_time")
            # Translate the local time as a bound variable, never a free
            # model constant. Restore the surrounding translator's bindings.
            elapsed = Real("__stlmc_bound_flow_time")
            previous = self.variables.get(elapsed)
            self.variables[elapsed] = time
            try:
                body = self.term(flow_condition_at_time(const, elapsed))
            finally:
                if previous is None:
                    del self.variables[elapsed]
                else:
                    self.variables[elapsed] = previous
            duration = self.term(Sub(const.end_tau, const.start_tau))
            guard = self.solver.mkTerm(Kind.AND,
                self.solver.mkTerm(Kind.GT, time, self.solver.mkReal(0)),
                self.solver.mkTerm(Kind.LT, time, duration))
            quantified = self.solver.mkTerm(Kind.FORALL,
                self.solver.mkTerm(Kind.VARIABLE_LIST, time),
                self.solver.mkTerm(Kind.IMPLIES, guard, body))
            bound = int(const.end_tau.id[4:]) - 1
            return self.solver.mkTerm(Kind.AND, self.term(Eq(
                Real("currentMode_{}".format(bound)),
                RealVal(str(const.current_mode_number)))), quantified)
        bound = str(int(const.end_tau.id[4:]) - 1)
        if not get_vars(const.const) or isinstance(const.const, Bool):
            return self.term(const.const)
        if isinstance(const.const, Not):
            return self.term(Forall(
                const.current_mode_number, const.end_tau, const.start_tau,
                reduce_not(const.const), const.integral,
            ))
        if isinstance(const.const, Implies):
            rewritten = Or([Not(const.const.left), const.const.right])
            return self.term(Forall(
                const.current_mode_number, const.end_tau, const.start_tau,
                rewritten, const.integral,
            ))
        if isinstance(const.const, (And, Or)):
            children = [
                self.term(child) if isinstance(child, Bool) or not get_vars(child)
                else self.term(Forall(
                    const.current_mode_number, const.end_tau, const.start_tau,
                    child, const.integral,
                ))
                for child in const.const.children
            ]
            kind = Kind.OR if isinstance(const.const, Or) else Kind.AND
            return children[0] if len(children) == 1 else self.solver.mkTerm(
                kind, *children
            )
        operators = {Gt: Gt, Geq: Geq, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq}
        operator = operators.get(type(const.const))
        if operator is None:
            raise NotSupportedError("unsupported forall expression {}".format(const.const))
        expression = Sub(const.const.left, const.const.right)
        invariant = reverse_inequality(operator(expression, RealVal("0")))
        expanded = make_forall_consts(Forall(
            const.current_mode_number, const.end_tau, const.start_tau,
            invariant, const.integral,
        ))
        return self.term(And([
            Eq(Real("currentMode_" + bound), RealVal(str(const.current_mode_number))),
            expanded,
        ]))


def cvc5Obj(const, solver=None):
    """Translate an STLmc constraint into a CVC5 term for adapter-level use."""
    active_solver = solver or cvc5.Solver()
    return _CVC5Translator(active_solver).term(const)


def _new_solver(logic):
    solver = cvc5.Solver()
    # OR flow invariants retain universal time quantification.
    solver.setLogic(logic[3:] if logic.startswith("QF_") else logic)
    solver.setOption("produce-models", "true")
    return solver


def _assignment_value(term, value):
    sort = term.getSort()
    if sort.isBoolean():
        return BoolVal(str(value.getBooleanValue()))
    if sort.isInteger():
        return IntVal(str(value.getIntegerValue()))
    if sort.isReal():
        return RealVal(str(value.getRealValue()))
    raise NotSupportedError("cannot translate CVC5 model value {}".format(value))


class _CVC5FormulaTranslator(_CVC5Translator):
    """Exact internal arithmetic without changing the final solver adapter."""

    def term(self, formula):
        if isinstance(formula, (RealVal, IntVal)):
            value = "99999" if formula.value == "inf" else formula.value
            fraction = Fraction(value)
            if isinstance(formula, RealVal):
                return self.solver.mkReal(str(fraction))
            if fraction.denominator != 1:
                raise NotSupportedError("non-integral IntVal")
            return self.solver.mkInteger(str(fraction.numerator))
        if isinstance(formula, Div):
            left, right = self.term(formula.left), self.term(formula.right)
            if left.getSort().isInteger() and right.getSort().isInteger():
                return self.solver.mkTerm(Kind.INTS_DIVISION, left, right)
        return super().term(formula)


class CVC5FormulaSolver(AssumptionFormulaSolver):
    """Independent incremental context with assumption-based core extraction."""

    def __init__(self, logic="QF_LRA"):
        self._init_state(logic)
        self._solver = _new_solver(logic)
        self._solver.setOption("incremental", "true")
        self._solver.setOption("produce-unsat-assumptions", "true")
        self._translator = _CVC5FormulaTranslator(self._solver)

    def _term(self, formula):
        return self._translator.term(formula)

    def _assert(self, term):
        self._solver.assertFormula(term)

    def _push(self):
        self._solver.push()

    def _pop(self):
        self._solver.pop()

    def _guard(self, term):
        # mkConst creates a fresh term; its display name is not an identity.
        guard = self._solver.mkConst(self._solver.getBooleanSort())
        self._assert(self._solver.mkTerm(Kind.IMPLIES, guard, term))
        return guard

    def _check(self, assumptions):
        result = (self._solver.checkSatAssuming(*assumptions)
                  if assumptions else self._solver.checkSat())
        if result.isSat():
            return SolverStatus.SAT
        if result.isUnsat():
            return SolverStatus.UNSAT
        return SolverStatus.UNKNOWN

    def _core(self):
        return self._solver.getUnsatAssumptions()

    def model(self):
        self._require_model()
        assignment = CVC5Assignment(solver=self._solver, translator=self._translator)
        return CVC5Assignment(
            {v: assignment.eval(v) for v in self._active_variables()},
            self._solver, self._translator,
        )


def _solve(const, logic):
    solver = _new_solver(logic)
    translator = _CVC5Translator(solver)
    solver.assertFormula(translator.term(const))
    status = solver.checkSat()
    if status.isSat():
        assignments = {
            variable: _assignment_value(term, solver.getValue(term))
            for variable, term in translator.variables.items()
        }
        return SolverStatus.SAT, assignments, None
    if status.isUnsat():
        return SolverStatus.UNSAT, {}, None
    return SolverStatus.UNKNOWN, {}, "CVC5 returned unknown"


def _parallel_cvc5_solve(const, logic, result_queue):
    try:
        result_queue.put(_solve(const, logic))
    except Exception as error:
        result_queue.put((
            SolverStatus.UNKNOWN, {}, "CVC5 worker error: {}".format(error)
        ))


class CVC5Solver(JobSolver):
    def submit(self, const, on_complete=None, query_name=""):
        job = SolverJob(on_complete)
        logic = self.config.get_section("cvc5").get_value("logic").upper()
        logic = logic[3:] if logic.startswith("QF_") else logic
        if is_enabled(self.config):
            solver = _new_solver(logic)
            translator = _CVC5Translator(solver)
            assertion = translator.term(const)
            sort_names = {"bool": "Bool", "int": "Int", "real": "Real"}
            lines = ["(set-logic {})".format(logic)]
            for variable in sorted(translator.variables, key=lambda item: item.id):
                lines.append("(declare-fun {} () {})".format(
                    variable.id, sort_names[variable.type]
                ))
            lines.extend([
                "(assert {})".format(assertion), "(check-sat)", "(get-model)",
            ])
            write_smt2(self.config, "cvc5", query_name, "\n".join(lines) + "\n")

        result_queue = multiprocessing.Queue()
        start_time = time.monotonic()
        process = multiprocessing.Process(
            target=_parallel_cvc5_solve, args=(const, logic, result_queue)
        )
        previous_sigint = None
        if hasattr(signal, "SIGINT"):
            previous_sigint = signal.signal(signal.SIGINT, signal.SIG_IGN)
        try:
            process.start()
        finally:
            if previous_sigint is not None:
                signal.signal(signal.SIGINT, previous_sigint)

        def collect_result():
            process.join()
            try:
                result, assignments, error = result_queue.get(timeout=0.2)
            except Empty:
                result, assignments = SolverStatus.UNKNOWN, {}
                error = "CVC5 worker exited with {}".format(process.exitcode)
            job.complete(SolveResult(
                result, CVC5Assignment(assignments),
                time.monotonic() - start_time, error, size_of_tree(const),
            ))
            result_queue.close()

        collector = threading.Thread(target=collect_result, daemon=True)
        job.set_worker(process, completion_worker=collector)
        collector.start()
        return job
