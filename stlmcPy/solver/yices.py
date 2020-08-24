from stlmcPy.constraints.operations import substitution_zero2t, diff, get_vars, reverse_inequality
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.abstract_solver import BaseSolver, SMTSolver

from yices import *
import yices_api as yapi
from stlmcPy.constraints.constraints import *
from functools import singledispatch


class YicesSolver(BaseSolver, SMTSolver):
    def __init__(self):
        self._yices_model = None

    def solve(self, all_consts, info_dict=None, boolean_abstract=None):
        result, size, self_yices_model = yicescheckSat(all_consts, 'QF_NRA')
        return result, size

    def make_assignment(self):
        pass

    def simplify(self, consts):
        pass

    def substitution(self, const, *dicts):
        pass


@singledispatch
def make_dynamics_consts(dyn: Ode):
    dyn_const_children = list()
    index = 0
    for exp in dyn.exps:
        var = dyn.vars[index]
        start_index = var.id[0:-2].find("_") + 1
        bound_str = var.id[start_index:-4]

        old_var_id = var.id[0: start_index - 1]
        new_end_var_id = old_var_id + "_" + bound_str + "_t"
        new_start_var_id = old_var_id + "_" + bound_str + "_0"

        new_end_var = Real(new_end_var_id)
        new_start_var = Real(new_start_var_id)

        end_tau_var = Real('tau_' + str(int(bound_str) + 1))
        start_tau_var = Real('tau_' + bound_str)

        new_exp_const = Eq(new_end_var, Add(new_start_var, Mul(Sub(end_tau_var, start_tau_var), exp)))
        dyn_const_children.append(new_exp_const)
        index += 1
    return And(dyn_const_children)


@make_dynamics_consts.register(Function)
def _(dyn: Function):
    dyn_const_children = list()
    index = 0
    for exp in dyn.exps:
        var = dyn.vars[index]
        start_index = var.id[0:-2].find("_") + 1
        bound_str = var.id[start_index:-4]

        old_var_id = var.id[0: start_index - 1]
        new_end_var_id = old_var_id + "_" + bound_str + "_t"

        new_end_var = Real(new_end_var_id)
        new_exp_const = Eq(new_end_var, exp)
        dyn_const_children.append(new_exp_const)
        index += 1
    return And(dyn_const_children)


def make_forall_consts_aux(forall: Forall):
    start_forall_exp = forall.const.left
    end_forall_exp = substitution_zero2t(forall.const.left)
    op_dict = {Gt: Gt, Geq: Geq}
    return And([forall.const,
                substitution_zero2t(forall.const),
                Implies(Eq(forall.const.left, RealVal('0')),
                        Forall(forall.current_mode_number,
                               forall.end_tau, forall.start_tau,
                               op_dict[forall.const.__class__](diff(start_forall_exp, forall.integral), RealVal('0')),
                               forall.integral)),
                Implies(Eq(end_forall_exp, RealVal('0')),
                        Forall(forall.current_mode_number,
                               forall.end_tau, forall.start_tau,
                               op_dict[forall.const.__class__](RealVal('0'), diff(start_forall_exp, forall.integral)),
                               forall.integral))])


def make_forall_consts(forall: Forall):
    if isinstance(forall.const, Bool) or len(get_vars(forall.const)) == 0:
        return forall.const
    if isinstance(forall.const, Eq):
        return And([forall.const, substitution_zero2t(forall.const),
                    Forall(forall.current_mode_number,
                           forall.end_tau, forall.start_tau,
                           Eq(diff(forall.const.left, forall.integral), RealVal('0')),
                           forall.integral)])
    elif isinstance(forall.const, Neq):
        first_const = make_forall_consts(Forall(forall.current_mode_number,
                                                forall.end_tau, forall.start_tau,
                                                Gt(forall.const.left, RealVal('0')),
                                                forall.integral))
        second_const = make_forall_consts(Forall(forall.current_mode_number,
                                                 forall.end_tau, forall.start_tau,
                                                 Gt(RealVal('0'), forall.const.left),
                                                 forall.integral))
        return Or([first_const, second_const])
    else:
        return make_forall_consts_aux(forall)


# return a check result and the Z3 constraint size
def yicescheckSat(consts, logic):
    strConsts = yicesObj(consts)
    cfg = Config()

    # TODO : current logic input is LRA, it should be QF_LRA
    if logic != "NONE":
        cfg.default_config_for_logic('QF_LRA')
    else:
        cfg.default_config_for_logic('QF_LRA')

    ctx = Context(cfg)

    yicesConsts = Terms.parse_term(strConsts)

    ctx.assert_formulas([yicesConsts])

    result = ctx.check_context()
    if result == Status.SAT:
        m = Model.from_context(ctx, 1)
        result = False
    else:
        m = None
        result = True if Status.UNSAT else "Unknown"

    cfg.dispose()
    ctx.dispose()

    return (result, -1, m)


# return the size of the Z3 constraint
def sizeAst(node: Terms):
    if node == Terms.NULL_TERM:
        return 0
    retval = yapi.yices_term_num_children(node)
    if retval == -1:
        return 0
    else:
        return 1 + sum([sizeAst(yapi.yices_term_child(node, c)) for c in range(retval)])


@singledispatch
def yicesObj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@yicesObj.register(RealVal)
def _(const: RealVal):
    return str(const.value)


@yicesObj.register(IntVal)
def _(const: IntVal):
    return str(const.value)


@yicesObj.register(BoolVal)
def _(const: BoolVal):
    if const.value == 'True':
        return 'true'
    elif const.value == 'False':
        return 'false'
    else:
        raise NotSupportedError("Z3 solver cannot translate this")


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
    return yicesObj(make_dynamics_consts(const.dynamics))


@yicesObj.register(Forall)
def _(const: Forall):
    bound_str = const.start_tau.id[3:]

    new_forall_const = const.const
    if not isinstance(const.const, Bool):
        op_dict = {Gt: Gt, Geq: Geq, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq}
        exp = Sub(const.const.left, const.const.right)
        new_forall_child_const = reverse_inequality(op_dict[const.const.__class__](exp, RealVal('0')))
        new_forall_const = make_forall_consts(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, new_forall_child_const, const.integral))
    new_const = And([Eq(Real("currentMode" + bound_str), RealVal(str(const.current_mode_number))),
                     new_forall_const])
    return yicesObj(new_const)
# ?????? return z3.And(z3Obj(new_const))



