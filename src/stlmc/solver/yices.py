import time
import re
from contextvars import ContextVar
from functools import singledispatch
from fractions import Fraction
from weakref import finalize

from .availability import load_yices_binding

load_yices_binding()
from yices import Config, Context, Model, Status, Terms, Types

from ..constraints.constraints import (
    Add, And, Bool, BoolVal, Constraint, Div, Eq, Forall, Geq, Gt,
    Implies, Int, IntVal, Integral, Leq, Lt, Mul, Neg, Neq, Not, Or, Pow,
    Real, RealVal, Sub, Variable,
)
from ..constraints.analysis import get_vars, size_of_tree
from ..constraints.logical_normalization import reduce_not
from ..constraints.normalization import reverse_inequality
from ..constraints.translation import make_forall_consts, make_dynamics_consts
from ..exceptions import NotSupportedError, SolverUnavailableError
from ..solver.abstract_solver import (
    JobSolver, SolveResult, SolverJob, SolverStatus, ThreadWorker,
)
from ..solver.assignment import Assignment
from .formula_state import AssumptionFormulaSolver
from ..utils.smt2_output import is_enabled, write_smt2


_query_variables = ContextVar("yices_query_variables", default=None)


def validate_yices_configuration(config):
    """Reject unsupported native execution modes before starting workers."""
    from yices import Yices

    common = config.get_section("common")
    parallel = str(common.get_value("parallel")).lower() == "true"
    if parallel and not Yices.is_thread_safe():
        raise SolverUnavailableError(
            "parallel Yices execution requires a thread-safe native library "
            "(including parallel-core=1). Run: stlmc-installer install --solver yices "
            "--build --thread-safe, or set common.parallel = false"
        )
    logic = config.get_section("yices").get_value("logic").upper()
    if logic in ("QF_NRA", "NRA", "QF_NIA", "NIA") and not Yices.has_mcsat():
        raise SolverUnavailableError(
            "Yices logic {} requires MCSAT, but the loaded library has no MCSAT. "
            "Run: stlmc-installer install --solver yices --build "
            "(omit --without-mcsat); use --thread-safe as well for parallel execution".format(logic)
        )


class YicesAssignment(Assignment):
    def __init__(self, _yices_model):
        self._yices_model = _yices_model

    # solver_model_to_generalized_model
    def get_assignments(self):
        new_dict = dict()
        if self._yices_model is None:
            return new_dict
        for e in self._yices_model.collect_defined_terms():
            # The pretty-printer truncates long generated identifiers at its
            # default width. Query the symbol itself, never its display text.
            name = Terms.get_name(e)
            if name is None:
                raise NotSupportedError("Yices model contains an unnamed variable")
            if Terms.is_real(e):
                new_dict[Real(name)] = RealVal(str(self._yices_model.get_float_value(e)))
            elif Terms.is_int(e):
                new_dict[Int(name)] = IntVal(str(self._yices_model.get_integer_value(e)))
            elif Terms.is_bool(e):
                new_dict[Bool(name)] = BoolVal(str(self._yices_model.get_bool_value(e)))
            else:
                NotSupportedError("cannot generate assignments")
        return new_dict

class _YicesFormulaAssignment(Assignment):
    def __init__(self, model, translator, variables):
        self._model = model
        self._release = finalize(self, model.dispose)
        self._translator = translator
        self._assignments = {v: self.eval(v) for v in variables}

    def get_assignments(self):
        return dict(self._assignments)

    def eval(self, formula):
        term = self._translator.term(formula)
        if Terms.is_bool(term):
            return BoolVal(str(self._model.get_bool_value(term)))
        # Native value terms retain arbitrarily large exact rationals; the
        # Python get_fraction_value wrapper is limited to rational64.
        value = self._model.get_value_as_term(term)
        if value < 0:
            raise NotSupportedError("Yices cannot produce an exact model value")
        width = 80
        text = Terms.to_string(value, width=width, height=0)
        while "..." in text:
            if width >= (1 << 30):
                raise NotSupportedError("Yices exact model value exceeds printer limits")
            width *= 2
            text = Terms.to_string(value, width=width, height=0)
        if self._translator.integer_expression(formula):
            return IntVal(str(int(Fraction(text))))
        if Terms.is_real(term):
            return RealVal(str(Fraction(text)))
        raise NotSupportedError("unsupported Yices model value")


class _YicesFormulaTranslator:
    """Native terms avoid the process-global symbol table used by yicesObj."""

    def __init__(self):
        self.variables = {}

    @classmethod
    def integer_expression(cls, formula):
        # Yices canonicalizes integral Real constants to integer terms. Keep
        # the Formula sort when selecting division and translating model values.
        if isinstance(formula, (Int, IntVal)):
            return True
        if isinstance(formula, Neg):
            return cls.integer_expression(formula.child)
        if isinstance(formula, (Add, Sub, Mul, Div)):
            return (cls.integer_expression(formula.left)
                    and cls.integer_expression(formula.right))
        return False

    def term(self, formula):
        if isinstance(formula, BoolVal):
            if formula.value not in ("True", "False"):
                raise NotSupportedError("invalid Boolean value")
            return Terms.true() if formula.value == "True" else Terms.false()
        if isinstance(formula, (RealVal, IntVal)):
            value = "99999" if formula.value == "inf" else formula.value
            fraction = Fraction(value)
            if isinstance(formula, IntVal) and fraction.denominator != 1:
                raise NotSupportedError("non-integral IntVal")
            return Terms.parse_rational(str(fraction))
        if isinstance(formula, Variable):
            if formula not in self.variables:
                sorts = {"bool": Types.bool_type, "real": Types.real_type,
                         "int": Types.int_type}
                self.variables[formula] = Terms.new_uninterpreted_term(sorts[formula.type]())
            return self.variables[formula]
        if isinstance(formula, (And, Or)):
            terms = [self.term(c) for c in formula.children]
            # Match STLmc's existing empty multinary convention.
            if not terms:
                return Terms.true()
            return Terms.yand(terms) if isinstance(formula, And) else Terms.yor(terms)
        if isinstance(formula, (Not, Neg)):
            return (Terms.ynot if isinstance(formula, Not) else Terms.neg)(self.term(formula.child))
        if isinstance(formula, Pow):
            try:
                exponent = Fraction(formula.right.value)
            except (AttributeError, ValueError, ZeroDivisionError) as error:
                raise NotSupportedError("Yices requires an integer exponent") from error
            if exponent.denominator != 1 or exponent < 0:
                raise NotSupportedError("Yices requires a non-negative integer exponent")
            return Terms.power(self.term(formula.left), int(exponent))
        if isinstance(formula, Div):
            operation = Terms.idiv if self.integer_expression(formula) else Terms.division
            return operation(self.term(formula.left), self.term(formula.right))
        operations = {
            Eq: Terms.eq, Neq: lambda a, b: Terms.ynot(Terms.eq(a, b)),
            Geq: Terms.arith_geq_atom, Gt: Terms.arith_gt_atom,
            Leq: Terms.arith_leq_atom, Lt: Terms.arith_lt_atom,
            Add: Terms.add, Sub: Terms.sub, Mul: Terms.mul,
            Div: Terms.division, Implies: Terms.implies,
        }
        if type(formula) in operations:
            return operations[type(formula)](self.term(formula.left), self.term(formula.right))
        raise NotSupportedError("unsupported incremental Yices formula: {}".format(type(formula)))


class YicesFormulaSolver(AssumptionFormulaSolver):
    """Exact incremental adapter with private unnamed variables and guards."""

    def __init__(self, logic="QF_LRA"):
        self._init_state(logic)
        self._config = Config()
        try:
            self._config.default_config_for_logic(logic)
            self._config.set_config("mode", "push-pop")
            self._context = Context(self._config)
        except BaseException:
            self._config.dispose()
            raise
        self._release = finalize(self, self._dispose_native, self._context, self._config)
        self._translator = _YicesFormulaTranslator()
        self._native_scopes = []

    @staticmethod
    def _dispose_native(context, config):
        try:
            context.dispose()
        finally:
            config.dispose()

    def _term(self, formula):
        return self._translator.term(formula)

    def _assert(self, term):
        # Virtual descendants must not write into the native parent scope:
        # even redundant extra assertions could change an assumptions core
        # into a background-only conflict that cannot be replayed after pop.
        if self._native_scopes and not self._native_scopes[-1]:
            return
        self._context.assert_formula(term)

    def _push(self):
        # Yices refuses push in its UNSAT state. Descendants only add
        # assertions/assumptions, so they remain UNSAT until this parent scope
        # is removed. Keep their logical scopes without a native push/pop.
        native = self._context.status() != Status.UNSAT
        if native:
            self._context.push()
        self._native_scopes.append(native)

    def _pop(self):
        if self._native_scopes[-1]:
            self._context.pop()
        self._native_scopes.pop()

    def _guard(self, term):
        guard = Terms.new_uninterpreted_term(Types.bool_type())
        self._assert(Terms.implies(guard, term))
        return guard

    def _check(self, assumptions):
        status = (self._context.check_context_with_assumptions(None, assumptions)
                  if assumptions else self._context.check_context())
        if status == Status.SAT:
            return SolverStatus.SAT
        if status == Status.UNSAT:
            return SolverStatus.UNSAT
        return SolverStatus.UNKNOWN

    def _core(self):
        return self._context.get_unsat_core()

    def model(self):
        self._require_model()
        return _YicesFormulaAssignment(
            Model.from_context(self._context, 1), self._translator,
            self._active_variables(),
        )


class YicesSolver(JobSolver):
    def __init__(self, config=None):
        if config is not None:
            validate_yices_configuration(config)
        JobSolver.__init__(self, config)
        self._logic_list = ["QF_LRA", "QF_NRA"]
        self._logic = "QF_NRA"

    def _set_logic(self, logic_name: str):
        self._logic = (logic_name.upper() if logic_name.upper() in self._logic_list else 'QF_NRA')

    def _write_query(self, consts, variables, query_name):
        if not is_enabled(self.config):
            return
        sort_names = {"bool": "Bool", "int": "Int", "real": "Real"}
        variables = sorted(variables, key=lambda variable: (variable.id, variable.type))
        names = {}
        for variable in variables:
            name = variable.id
            if not re.fullmatch(r"[A-Za-z~!@$%^&*_+=<>.?/\-][A-Za-z0-9~!@$%^&*_+=<>.?/\-]*", name):
                if "|" in name or "\\" in name:
                    raise NotSupportedError("cannot export SMT2 symbol: {}".format(name))
                name = "|{}|".format(name)
            names[variable.id] = name
        lines = ["(set-logic {})".format(self._logic)]
        for variable in variables:
            lines.append("(declare-fun {} () {})".format(
                names[variable.id], sort_names[variable.type]
            ))
        for const in consts:
            # Yices accepts generated names containing braces/commas that
            # SMT-LIB requires to be quoted. Replace whole tokens only.
            const = re.sub(r"[^\s()]+", lambda match: names.get(
                match.group(0), match.group(0)), const)
            lines.append("(assert {})".format(const))
        lines.extend(["(check-sat)", "(get-model)"])
        write_smt2(
            self.config, "yices", query_name, "\n".join(lines) + "\n"
        )

    def submit(self, const, on_complete=None, query_name=""):
        validate_yices_configuration(self.config)
        job = SolverJob(on_complete)
        logic = self.config.get_section("yices").get_value("logic")
        self._set_logic(logic)
        if is_enabled(self.config):
            # Collect symbols from the actual lowering, not the raw tree:
            # Integral is a structural marker, and lowering introduces clocks
            # and mode variables absent from get_vars(raw_constraint).
            variables = set()
            token = _query_variables.set(variables)
            try:
                query = yicesObj(const)
            finally:
                _query_variables.reset(token)
            self._write_query([query], variables, query_name)
        worker = ThreadWorker()
        start_time = time.monotonic()

        def check_sat():
            error_message = None
            try:
                logic = self.config.get_section("yices").get_value("logic").upper()
                cfg = Config()
                cfg.default_config_for_logic(logic)
                ctx = Context(cfg)
                ctx.assert_formulas([Terms.parse_term(yicesObj(const))])
                status = ctx.check_context()
                if status == Status.SAT:
                    result = SolverStatus.SAT
                    assignment = YicesAssignment(Model.from_context(ctx, 1))
                elif status == Status.UNSAT:
                    result = SolverStatus.UNSAT
                    assignment = YicesAssignment(None)
                else:
                    result = SolverStatus.UNKNOWN
                    assignment = YicesAssignment(None)
                    error_message = "Yices returned {}".format(status)
                ctx.dispose()
                cfg.dispose()
            except Exception as error:
                result = SolverStatus.UNKNOWN
                assignment = YicesAssignment(None)
                error_message = "parallel Yices worker error: {}".format(error)
            finally:
                elapsed = time.monotonic() - start_time
                worker.finish()
                # Completion must always be reported so the runner can release
                # its capacity token, including when cancellation won the race.
                job.complete(SolveResult(
                    result, assignment, elapsed, error_message,
                    size_of_tree(const),
                ))

        job.set_worker(worker, kind="thread")
        worker.start(check_sat)
        return job

@singledispatch
def yicesObj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@yicesObj.register(RealVal)
def _(const: RealVal):
    if const.value == "inf":
        return "99999"
    return str(const.value)


@yicesObj.register(IntVal)
def _(const: IntVal):
    if const.value == "inf":
        return "99999"
    return str(const.value)


@yicesObj.register(BoolVal)
def _(const: BoolVal):
    if const.value == 'True':
        return 'true'
    elif const.value == 'False':
        return 'false'
    else:
        raise NotSupportedError("Yices solver cannot translate this")


@yicesObj.register(Variable)
def _(const: Variable):
    variables = _query_variables.get()
    if variables is not None:
        variables.add(const)
    op = {'bool': Types.bool_type(), 'real': Types.real_type(), 'int': Types.int_type()}
    x = Terms.new_uninterpreted_term(op[const.type], str(const.id))

    return str(const.id)


@yicesObj.register(Geq)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(>= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Gt)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(> ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Leq)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(<= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Lt)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(< ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Eq)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(= ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Neq)
def _(const):
    reduceNot = Not(Eq(const.left, const.right))
    return yicesObj(reduceNot)


@yicesObj.register(Add)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(+ ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Sub)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(- ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Pow)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)

    cfg = Config()
    cfg.default_config_for_logic('QF_LRA')
    ctx = Context(cfg)
    red_val = Terms.new_uninterpreted_term(Types.real_type(), 'red')
    red = Terms.parse_term('(= red ' + y + ')')
    ctx.assert_formulas([red])
    status = ctx.check_context()

    if status == Status.SAT:
        model = Model.from_context(ctx, 1)
        yval = str(model.get_value(red_val))
    else:
        raise NotSupportedError("something wrong in divisor of power")
    cfg.dispose()
    ctx.dispose()
    result = '(^ ' + x + ' ' + yval + ')'
    return result


@yicesObj.register(Mul)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(* ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Div)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(/ ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Neg)
def _(const):
    x = yicesObj(const.child)
    result = '(- ' + str(0) + ' ' + x + ')'
    return result


@yicesObj.register(And)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(and ' + ' '.join(yicesargs) + ')'
        return result


@yicesObj.register(Or)
def _(const):
    yicesargs = [yicesObj(c) for c in const.children]
    if len(yicesargs) < 1:
        return 'true'
    elif len(yicesargs) < 2:
        return yicesargs[0]
    else:
        result = '(or ' + ' '.join(yicesargs) + ')'
        return result


@yicesObj.register(Implies)
def _(const):
    x = yicesObj(const.left)
    y = yicesObj(const.right)
    result = '(=> ' + x + ' ' + y + ')'
    return result


@yicesObj.register(Not)
def _(const):
    x = yicesObj(const.child)
    result = '(not ' + x + ')'
    return result


@yicesObj.register(Integral)
def _(const: Integral):
    res = yicesObj(make_dynamics_consts(const.dynamics))

    return res


@yicesObj.register(Forall)
def _(const: Forall):
    if isinstance(const.const, (Or, Implies)):
        from ..constraints.quantified_flow import eliminate_boolean_flow_condition
        return yicesObj(eliminate_boolean_flow_condition(const))
    bound_str = str(int(const.end_tau.id[4:]) - 1)

    if len(get_vars(const.const)) == 0:
        return yicesObj(const.const)

    new_forall_const = const.const
    if isinstance(const.const, Bool):
        return yicesObj(const.const)
    if get_vars(const.const) is None:
        return yicesObj(const.const)
    if isinstance(const.const, Not):
        if isinstance(const.const.child, Bool):
            return "(not " + yicesObj(const.const.child) + ")"
        if isinstance(const.const.child, Not):
            return yicesObj(const.const.child.child)
        reduced_const = reduce_not(const.const)
        new_const = yicesObj(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, reduced_const, const.integral))
        return new_const
    elif isinstance(const.const, Implies):
        left = reduce_not(Not(const.const.left))
        right = const.const.right
        left_new = yicesObj(Forall(const.current_mode_number, const.end_tau, const.start_tau, left, const.integral))
        right_new = yicesObj(Forall(const.current_mode_number, const.end_tau, const.start_tau, right, const.integral))
        return "(or " + yicesObj(left_new) + " " + yicesObj(right_new) + ")"
    elif isinstance(const.const, And) or isinstance(const.const, Or):
        result = list()
        for c in const.const.children:
            if isinstance(c, Bool):
                result.append(yicesObj(c))
            elif get_vars(c) is None:
                result.append(yicesObj(c))
            else:
                result.append(
                    yicesObj(Forall(const.current_mode_number, const.end_tau, const.start_tau, c, const.integral)))

        if isinstance(const.const, Or):
            return '(or ' + ' '.join(result) + ')'
        else:
            return '(and ' + ' '.join(result) + ')'
    elif not isinstance(const.const, Bool):
        op_dict = {Gt: Gt, Geq: Geq, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq}
        exp = Sub(const.const.left, const.const.right)
        new_forall_child_const = reverse_inequality(op_dict[const.const.__class__](exp, RealVal('0')))
        new_forall_const = make_forall_consts(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, new_forall_child_const, const.integral))
    new_const = And([Eq(Real("currentMode_" + bound_str), RealVal(str(const.current_mode_number))),
                     new_forall_const])
    return yicesObj(new_const)
