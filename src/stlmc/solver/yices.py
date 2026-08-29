import time

from yices import *

from ..constraints.constraints import *
from ..constraints.operations import *
from ..constraints.translation import make_forall_consts, make_dynamics_consts
from ..exception.exception import NotSupportedError
from ..solver.abstract_solver import (
    SMTSolver, ParallelSMTSolver, SolveResult, SolverJob, ThreadWorker,
)
from ..solver.assignment import Assignment
from ..util.smt2_output import is_enabled, write_smt2
from ..tree.operations import size_of_tree


class YicesAssignment(Assignment):
    def __init__(self, _yices_model):
        self._yices_model = _yices_model

    # solver_model_to_generalized_model
    def get_assignments(self):
        new_dict = dict()
        if self._yices_model is None:
            return new_dict
        for e in self._yices_model.collect_defined_terms():
            if Terms.is_real(e):
                new_dict[Real(Terms.to_string(e))] = RealVal(str(self._yices_model.get_float_value(e)))
            elif Terms.is_int(e):
                new_dict[Int(Terms.to_string(e))] = IntVal(str(self._yices_model.get_integer_value(e)))
            elif Terms.is_bool(e):
                new_dict[Bool(Terms.to_string(e))] = BoolVal(str(self._yices_model.get_bool_value(e)))
            else:
                NotSupportedError("cannot generate assignments")
        return new_dict

    def eval(self, const):
        pass


class YicesSolver(ParallelSMTSolver):
    def __init__(self):
        SMTSolver.__init__(self)
        self._yices_model = None
        self._cache = list()
        self._cache_raw = list()
        self._logic_list = ["QF_LRA", "QF_NRA"]
        self._logic = "QF_NRA"
        self.set_time("solving timer", 0)
        self.file_name = ""
        self._last_assignment = None

    def set_logic(self, logic_name: str):
        self._logic = (logic_name.upper() if logic_name.upper() in self._logic_list else 'QF_NRA')

    def _write_query(self, consts, raw_constraint):
        if not is_enabled(self.config):
            return
        sort_names = {"bool": "Bool", "int": "Int", "real": "Real"}
        variables = sorted(get_vars(raw_constraint), key=lambda variable: variable.id)
        lines = ["(set-logic {})".format(self._logic)]
        for variable in variables:
            lines.append("(declare-fun {} () {})".format(
                variable.id, sort_names[variable.type]
            ))
        for const in consts:
            lines.append("(assert {})".format(const))
        lines.extend(["(check-sat)", "(get-model)"])
        write_smt2(
            self.config, "yices", self.file_name, "\n".join(lines) + "\n"
        )

    def make_assignment(self):
        if self._last_assignment is not None:
            return self._last_assignment
        return YicesAssignment(self._yices_model)

    def clear(self):
        self._cache = list()
        self._cache_raw = list()

    def simplify(self, consts):
        pass

    def substitution(self, const, *dicts):
        pass

    def add(self, const):
        pass

    def set_time_bound(self, time_bound: str):
        pass

    def set_file_name(self, name):
        self.file_name = name

    def submit(self, const, on_complete=None):
        job = SolverJob(on_complete)
        logic = self.config.get_section("yices").get_value("logic")
        self.set_logic(logic)
        self._write_query([yicesObj(const)], const)
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
                    result = "False"
                    assignment = YicesAssignment(Model.from_context(ctx, 1))
                elif status == Status.UNSAT:
                    result = "True"
                    assignment = YicesAssignment(None)
                else:
                    result = "Unknown"
                    assignment = YicesAssignment(None)
                    error_message = "Yices returned {}".format(status)
                ctx.dispose()
                cfg.dispose()
            except Exception as error:
                result = "Unknown"
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

        job.set_worker(worker)
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
