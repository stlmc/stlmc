import asyncio
import subprocess
import threading
from multiprocessing import Process
from queue import Queue

from yices import *

from ..constraints.constraints import *
from ..constraints.operations import *
from ..constraints.translation import make_forall_consts, make_dynamics_consts
from ..exception.exception import NotSupportedError
from ..solver.abstract_solver import SMTSolver, ParallelSMTSolver
from ..solver.assignment import Assignment
from ..tree.operations import size_of_tree


class YicesAssignment(Assignment):
    def __init__(self, _yices_model):
        self._yices_model = _yices_model

    # solver_model_to_generalized_model
    def get_assignments(self):
        new_dict = dict()
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

    def set_logic(self, logic_name: str):
        self._logic = (logic_name.upper() if logic_name.upper() in self._logic_list else 'QF_NRA')

    async def _run(self, consts, logic):
        try:
            return await asyncio.wait_for(self._yicescheckSat(consts, logic), timeout=100000000.0)
        except asyncio.TimeoutError:
            print('timeout!')

    def yicescheckSat(self, consts, logic):
        return asyncio.run(self._run(consts, logic))

    async def _yicescheckSat(self, consts, logic):
        assert self.logger is not None
        logger = self.logger

        common_section = self.config.get_section("yices")
        logic = common_section.get_value("logic")
        self._logic = logic.upper()

        cfg = Config()

        # TODO : current logic input is LRA, it should be QF_NRA
        if logic != "NONE":
            cfg.default_config_for_logic(self._logic)
        else:
            cfg.default_config_for_logic(self._logic)

        ctx = Context(cfg)
        yicesConsts = list()
        for i in range(len(consts)):
            yicesConsts.append(Terms.parse_term(consts[i]))

        logger.start_timer("solving timer")
        ctx.assert_formulas(yicesConsts)

        result = ctx.check_context()

        logger.stop_timer("solving timer")
        self.set_time("solving timer", logger.get_duration_time("solving timer"))

        if result == Status.SAT:
            m = Model.from_context(ctx, 1)
            result = "False"
        else:
            m = None
            result = "True" if Status.UNSAT else "Unknown"

        cfg.dispose()
        ctx.dispose()

        return result, m

    def solve(self, all_consts=None, info_dict=None, boolean_abstract=None):
        yices_section = self.config.get_section("yices")
        logic = yices_section.get_value("logic")
        self.set_logic(logic)

        if all_consts is not None:
            self._cache_raw.append(all_consts)
            self._cache.append(yicesObj(all_consts))
        size = size_of_tree(And(self._cache_raw))
        result, self._yices_model = self.yicescheckSat(self._cache, self._logic)
        return result, size

    def make_assignment(self):
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

    def process(self, main_queue: Queue, sema: threading.Semaphore, const):
        proc = Process()
        proc.start()
        check_sat_thread = threading.Thread(target=self.parallel_check_sat, args=(main_queue, sema, proc))
        check_sat_thread.daemon = True
        check_sat_thread.start()

        return proc

    def parallel_check_sat(self, main_queue: Queue, sema: threading.Semaphore, proc: subprocess.Popen, const):
        common_section = self.config.get_section("yices")
        logic = common_section.get_value("logic")
        self._logic = logic.upper()
        # print(logic)
        cfg = Config()
        yices_consts = yicesObj(const)

        # TODO : current logic input is LRA, it should be QF_NRA
        if logic != "NONE":
            cfg.default_config_for_logic(self._logic)
        else:
            cfg.default_config_for_logic(self._logic)

        ctx = Context(cfg)
        yicesConsts = [Terms.parse_term(yices_consts)]
        ctx.assert_formulas(yicesConsts)

        result = ctx.check_context()

        if result == Status.SAT:
            m = Model.from_context(ctx, 1)
            result = "False"
        else:
            m = None
            result = "True" if Status.UNSAT else "Unknown"

        cfg.dispose()
        ctx.dispose()

        main_queue.put((result, YicesAssignment(m), id(proc)))
        sema.release()


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
