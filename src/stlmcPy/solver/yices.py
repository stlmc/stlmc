import yices_api
from yices import *

from ..constraints.aux.operations import *
from ..constraints.translation import make_forall_consts, make_dynamics_consts
from ..exception.exception import NotSupportedError
from ..objects.configuration import Configuration
from ..solver.abstract_solver import SMTSolver
from ..solver.assignment import Assignment
from ..tree.operations import size_of_tree


class YicesSolver(SMTSolver):
    def __init__(self, config: Configuration):
        SMTSolver.__init__(self)

        yices_section = config.get_section("yices")
        logic = yices_section.get_value("logic")

        self._cfg: Config = Config()
        self._cfg.default_config_for_logic(logic.upper())

        self._ctx: Context = Context(self._cfg)
        self._model = None

    def __del__(self):
        self._ctx.dispose()
        self._cfg.dispose()

    def check_sat(self, *assumption, **information):
        self._clear_model()

        if len(assumption) > 0:
            status = self._ctx.check_context(translate(And([c for c in assumption])))
        else:
            status = self._ctx.check_context()

        if status == Status.SAT:
            m = Model.from_context(self._ctx, 1)
            result = SMTSolver.sat
        elif status == Status.UNSAT:
            m = None
            result = SMTSolver.unsat
        else:
            m = None
            result = SMTSolver.unknown
        return result, m

    def make_assignment(self):
        if self._model is None:
            raise Exception("Yices solver error occurred during making assignment (no model exists)")
        return YicesAssignment(self._model)

    def push(self):
        self._ctx.push()

    def pop(self):
        self._ctx.pop()

    def reset(self):
        self._ctx.reset_context()

    def add(self, formula: Formula):
        self._ctx.assert_formula(translate(formula))

    def assert_and_track(self, formula: Formula, track_id: str):
        pass

    def unsat_core(self):
        return self._ctx.get_unsat_core()

    def _clear_model(self):
        if self._model is not None:
            self._model.dispose()
            self._model = None


class YicesAssignment(Assignment):
    def __init__(self, _yices_model: Model):
        Assignment.__init__(self)
        self._yices_model: Model = _yices_model

    def _get_assignments(self):
        new_dict = dict()
        for e in self._yices_model.collect_defined_terms():
            var_id = Terms.to_string(e)
            if Terms.is_real(e):
                new_dict[Real(var_id)] = RealVal(str(self._yices_model.get_float_value(e)))
            elif Terms.is_int(e):
                new_dict[Int(var_id)] = IntVal(str(self._yices_model.get_integer_value(e)))
            elif Terms.is_bool(e):
                new_dict[Bool(var_id)] = BoolVal(str(self._yices_model.get_bool_value(e)))
            else:
                NotSupportedError("cannot generate assignments")
        return new_dict

    def eval(self, const: Formula):
        val = self._yices_model.formula_true_in_model(translate(const))
        if val is True:
            return Assignment.true
        else:
            return Assignment.false


@singledispatch
def translate(const: Union[Formula, Expr]):
    raise NotSupportedError("fail to translate \"{}\" to Yices object ".format(const))


@translate.register(Constant)
def _(const: Constant):
    if const.value == "inf":
        return "99999"
    return str(const.value)


@translate.register(Variable)
def _(var: Variable):
    return var.id


@translate.register(Not)
def _(const: Not):
    return "(not {})".format(translate(const.child))


@translate.register(Neq)
def _(const: Neq):
    not_const = Not(Eq(const.left, const.right))
    return translate(not_const)


@translate.register(Neg)
def _(const: Neg):
    return "(- 0 {})".format(translate(const.child))


@translate.register(Binary)
def _(const):
    return "({} {} {})".format(const.type, translate(const.left), translate(const.right))


@translate.register(Multinary)
def _(const: Multinary):
    args = [translate(c) for c in const.children]
    if len(args) < 1:
        return 'true'
    elif len(args) == 1:
        return args[0]
    else:
        return "({} {})".format(const.type, " ".join(args))


@translate.register(Integral)
def _(const: Integral):
    res = translate(make_dynamics_consts(const.dynamics))
    return res


@translate.register(Forall)
def _(const: Forall):
    bound_str = str(int(const.end_tau.id[4:]) - 1)

    if len(get_vars(const.const)) == 0:
        return translate(const.const)

    new_forall_const = const.const
    if isinstance(const.const, Bool):
        return translate(const.const)
    if get_vars(const.const) is None:
        return translate(const.const)
    if isinstance(const.const, Not):
        if isinstance(const.const.child, Bool):
            return "(not " + translate(const.const.child) + ")"
        if isinstance(const.const.child, Not):
            return translate(const.const.child.child)
        reduced_const = reduce_not(const.const)
        new_const = translate(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, reduced_const, const.integral))
        return new_const
    elif isinstance(const.const, Implies):
        left = reduce_not(Not(const.const.left))
        right = const.const.right
        left_new = translate(Forall(const.current_mode_number, const.end_tau, const.start_tau, left, const.integral))
        right_new = translate(Forall(const.current_mode_number, const.end_tau, const.start_tau, right, const.integral))
        return "(or " + translate(left_new) + " " + translate(right_new) + ")"
    elif isinstance(const.const, And) or isinstance(const.const, Or):
        result = list()
        for c in const.const.children:
            if isinstance(c, Bool):
                result.append(translate(c))
            elif get_vars(c) is None:
                result.append(translate(c))
            else:
                result.append(
                    translate(Forall(const.current_mode_number, const.end_tau, const.start_tau, c, const.integral)))

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
    return translate(new_const)