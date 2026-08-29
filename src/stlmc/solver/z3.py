import threading
import time
import multiprocessing
import signal
from queue import Empty
from queue import Queue

import z3

from ..constraints.operations import *
from ..constraints.translation import make_forall_consts, make_dynamics_consts
from ..exception.exception import NotSupportedError
from ..solver.abstract_solver import (
    IncrementalFormulaSolver, JobSolver, SolveResult, SolverJob,
    SolverStatus,
)
from ..solver.assignment import Assignment
from ..util.smt2_output import is_enabled, write_smt2
from ..tree.operations import size_of_tree


class Z3Solver(JobSolver):
    def __init__(self):
        JobSolver.__init__(self)
        self._logic_dict = dict()
        self._logic_dict["QF_NRA"] = "NRA"
        self._logic_dict["QF_LRA"] = "LRA"
        self._logic = "NRA"

        self.file_name = ""
        self._last_assignment = None

    def set_logic(self, logic_name: str):
        self._logic = (self._logic_dict[logic_name.upper()] if logic_name.upper() in self._logic_dict else "NRA")

    def clear(self):
        self._last_assignment = None

    def set_file_name(self, name):
        self.file_name = name

    def submit(self, const, on_complete=None):
        job = SolverJob(on_complete)
        self.set_logic(self.config.get_section("z3").get_value("logic"))
        if is_enabled(self.config):
            dump_solver = z3.SolverFor(self._logic)
            dump_solver.add(z3Obj(const))
            write_smt2(self.config, "z3", self.file_name, dump_solver.to_smt2())
        result_queue = multiprocessing.Queue()
        start_time = time.monotonic()
        proc = multiprocessing.Process(
            target=_parallel_z3_solve,
            args=(const, self._logic, result_queue),
        )
        previous_sigint = None
        if hasattr(signal, "SIGINT"):
            previous_sigint = signal.signal(signal.SIGINT, signal.SIG_IGN)
        try:
            proc.start()
        finally:
            if previous_sigint is not None:
                signal.signal(signal.SIGINT, previous_sigint)

        def collect_result():
            proc.join()
            try:
                result, assignments, error_message = result_queue.get(timeout=0.2)
            except Empty:
                result = "Unknown"
                assignments = dict()
                error_message = "parallel Z3 worker exited with {}".format(proc.exitcode)
            elapsed = time.monotonic() - start_time
            job.complete(SolveResult(
                result, Z3Assignment(assignments=assignments),
                elapsed, error_message, size_of_tree(const),
            ))
            result_queue.close()

        collector = threading.Thread(target=collect_result, daemon=True)
        proc._stlmc_worker = collector
        job.set_worker(proc)
        collector.start()
        return job

    def make_assignment(self):
        return self._last_assignment


class Z3FormulaSolver(IncrementalFormulaSolver):
    """Incremental Z3 adapter whose public API only accepts STLmc formulas."""

    def __init__(self, logic="QF_LRA"):
        self.logic = logic
        self._solver = z3.SolverFor(logic)
        self._assertions = []
        self._tracked = {}
        self._scopes = []

    def add(self, formula):
        self._assertions.append(formula)
        self._solver.add(z3Obj(formula))

    def push(self):
        self._scopes.append((len(self._assertions), set(self._tracked)))
        self._solver.push()

    def pop(self):
        assertion_size, track_ids = self._scopes.pop()
        del self._assertions[assertion_size:]
        self._tracked = {
            key: value for key, value in self._tracked.items()
            if key in track_ids
        }
        self._solver.pop()

    def check(self):
        result = self._solver.check()
        if result == z3.sat:
            return SolverStatus.SAT
        if result == z3.unsat:
            return SolverStatus.UNSAT
        return SolverStatus.UNKNOWN

    def model(self):
        return Z3Assignment(self._solver.model())

    def track(self, formula, track_id):
        self._tracked[track_id] = formula
        self._solver.assert_and_track(z3Obj(formula), track_id)

    def unsat_core(self):
        return {str(item) for item in self._solver.unsat_core()}

    def fork(self):
        result = Z3FormulaSolver(self.logic)
        for formula in self._assertions:
            result.add(formula)
        return result

class Z3Assignment(Assignment):
    def __init__(self, z3_model=None, assignments=None):
        self._z3_model = z3_model
        self._assignments = assignments

    # solver_model_to_generalized_model
    def get_assignments(self):
        if self._assignments is not None:
            return self._assignments
        if self._z3_model is None:
            return dict()
        new_dict = dict()
        op_var_dict = {'bool': Bool, 'int': Int, 'real': Real}
        op_dict = {'bool': BoolVal, 'int': IntVal, 'real': RealVal}
        for d in self._z3_model.decls():
            var_type_str = str(d.range()).lower()
            new_var = op_var_dict[var_type_str](d.name())
            z3_val = self._z3_model[d]
            new_dict[new_var] = op_dict[var_type_str](str(z3_val).replace("?", ""))
        return new_dict

    def eval(self, const):
        if self._z3_model is None:
            raise NotSupportedError("Z3 has no model")
        value = self._z3_model.eval(z3Obj(const), model_completion=True)
        if z3.is_true(value):
            return BoolVal("True")
        if z3.is_false(value):
            return BoolVal("False")
        if z3.is_int_value(value):
            return IntVal(str(value))
        if z3.is_rational_value(value):
            return RealVal(str(value).replace("?", ""))
        raise NotSupportedError("cannot translate Z3 model value {}".format(value))

def _parallel_z3_solve(const, logic, result_queue):
    """Solve in an isolated process because Z3's global context is not thread-safe."""
    try:
        solver = z3.SolverFor(logic)
        solver.add(z3Obj(const))
        status = solver.check()
        if status == z3.sat:
            result_queue.put(("False", Z3Assignment(solver.model()).get_assignments(), None))
        elif status == z3.unsat:
            result_queue.put(("True", dict(), None))
        else:
            result_queue.put(("Unknown", dict(),
                              "Z3 returned unknown: {}".format(solver.reason_unknown())))
    except Exception as error:
        result_queue.put(("Unknown", dict(), "parallel Z3 worker error: {}".format(error)))


@singledispatch
def z3Obj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@z3Obj.register(RealVal)
def _(const: RealVal):
    if const.value == "inf":
        return z3.RealVal("99999")
    return z3.RealVal(const.value)


@z3Obj.register(IntVal)
def _(const: IntVal):
    if const.value == "inf":
        return z3.IntVal("99999")
    return z3.IntVal(const.value)


@z3Obj.register(BoolVal)
def _(const: BoolVal):
    if const.value == 'True':
        return z3.BoolVal(True)
    elif const.value == 'False':
        return z3.BoolVal(False)
    else:
        raise NotSupportedError("Z3 solver cannot translate this")


@z3Obj.register(Variable)
def _(const: Variable):
    op = {'bool': z3.Bool, 'real': z3.Real, 'int': z3.Int}
    return op[const.type](const.id)


@z3Obj.register(Geq)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x >= y


@z3Obj.register(Gt)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x > y


@z3Obj.register(Leq)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x <= y


@z3Obj.register(Lt)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x < y


@z3Obj.register(Eq)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x == y


@z3Obj.register(Neq)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x != y


@z3Obj.register(Add)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x + y


@z3Obj.register(Sub)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x - y


@z3Obj.register(Pow)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x ** y


@z3Obj.register(Mul)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x * y


@z3Obj.register(Div)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return x / y


@z3Obj.register(Neg)
def _(const):
    x = z3Obj(const.child)
    return -x


@z3Obj.register(And)
def _(const):
    z3args = [z3Obj(c) for c in const.children]
    if len(z3args) < 1:
        return z3.BoolVal(True)
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.And(z3args)


@z3Obj.register(Or)
def _(const):
    z3args = [z3Obj(c) for c in const.children]
    if len(z3args) < 1:
        return z3.BoolVal(True)
    elif len(z3args) < 2:
        return z3args[0]
    else:
        return z3.Or(z3args)


@z3Obj.register(Implies)
def _(const):
    x = z3Obj(const.left)
    y = z3Obj(const.right)
    return z3.Implies(x, y)


@z3Obj.register(Not)
def _(const):
    x = z3Obj(const.child)
    return z3.Not(x)


@z3Obj.register(Integral)
def _(const: Integral):
    return z3Obj(make_dynamics_consts(const.dynamics))


@z3Obj.register(Forall)
def _(const: Forall):
    bound_str = str(int(const.end_tau.id[4:]) - 1)

    if len(get_vars(const.const)) == 0:
        return z3Obj(const.const)

    new_forall_const = const.const
    if isinstance(const.const, Bool):
        return z3Obj(const.const)
    if get_vars(const.const) is None:
        return z3Obj(const.const)
    if isinstance(const.const, Not):
        if isinstance(const.const.child, Bool):
            return "(not " + z3Obj(const.const.child) + ")"
        if isinstance(const.const.child, Not):
            return z3Obj(const.const.child.child)
        reduced_const = reduce_not(const.const)
        new_const = z3Obj(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, reduced_const, const.integral))
        return new_const
    elif isinstance(const.const, Implies):
        left = reduce_not(Not(const.const.left))
        right = const.const.right
        left_new = z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, left, const.integral))
        right_new = z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, right, const.integral))
        return "(or " + z3Obj(left_new) + " " + z3Obj(right_new) + ")"
    elif isinstance(const.const, And) or isinstance(const.const, Or):
        result = list()
        for c in const.const.children:
            if isinstance(c, Bool):
                result.append(z3Obj(c))
            elif get_vars(c) is None:
                result.append(z3Obj(c))
            else:
                result.append(
                    z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, c, const.integral)))

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
    return z3Obj(new_const)
