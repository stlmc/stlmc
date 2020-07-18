from functools import singledispatch

import z3

from stlmcPy.constraints.operations import get_vars, substitution, make_dict, reverse_inequality, diff, \
    substitution_zero2t
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.abstract_solver import BaseSolver
from stlmcPy.constraints.constraints import *


class Z3Solver(BaseSolver):
    def solve(self, all_consts):
        return z3checkSat(all_consts, 'LRA')


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


def make_forall_consts(const: Constraint,
                       current_mode_num,
                       end_tau, start_tau,
                       flow):
    var_set = get_vars(const)

    if len(var_set):
        return const

    # If proposition is just boolean variable, return original expression
    if not (isinstance(const, Gt) or isinstance(const, Geq) or
            isinstance(const, Lt) or isinstance(const, Leq) or
            isinstance(const, Eq) or isinstance(const, Neq) or
            isinstance(const, Bool)):
        raise NotSupportedError("make for all consts type error")

    if isinstance(const, Bool):
        return const

    new_const = reverse_inequality(const)

    result = list()
    exp = Sub(new_const.left, new_const.right)
    diff_exp = diff(exp)
    end_exp = substitution_zero2t(exp)

    # monotone increase or decrease
    result.append(Or([Geq(diff_exp, RealVal("0")), Leq(diff_exp, RealVal("0"))]))

    # Special case : a == b
    if isinstance(exp, Eq):
        result.append(Neq(exp, RealVal("0")))
        result.append(Neq(substitution_zero2t(exp), RealVal("0")))
        result.append(Neq(diff_exp, RealVal("0")))
    # Special case : a =/= b
    elif isinstance(exp, Neq):
        sub_result = list()
        sub_result.append(
            Forall(current_mode_num, end_tau, start_tau, Gt(exp, RealVal("0")), flow))
        sub_result.append(
            Forall(current_mode_num, end_tau, start_tau, Lt(exp, RealVal("0")), flow))
        result.append(Or(sub_result))
    else:
        # f(t') >= 0
        result.append(Geq(end_exp, RealVal("0")))
        if isinstance(exp, Gt):
            # Check a start point of interval satisfies the proposition
            result.append(Gt(exp, RealVal("0")))
            # Case : f(t) = 0 -> dot(f(T)) > 0, forall T in (t, t')
            result.append(Implies(Eq(exp, RealVal("0")),
                                  Forall(current_mode_num, end_tau, start_tau, Gt(diff_exp, RealVal("0")), flow)))
            # Case : f(t') = 0 -> dot(f(T)) < 0, forall T in (t, t')
            result.append(Implies(end_exp == RealVal(0),
                                  Forall(current_mode_num, end_tau, start_tau, Lt(diff_exp, RealVal("0")), flow)))
        elif isinstance(exp, Geq):
            result.append(Geq(exp, RealVal("0")))
            result.append(Implies(Eq(exp, RealVal("0")),
                                  Forall(current_mode_num, end_tau, start_tau, Geq(diff_exp, RealVal("0")), flow)))
            result.append(Implies(Eq(end_exp, RealVal("0")),
                                  Forall(current_mode_num, end_tau, start_tau, Leq(diff_exp, RealVal("0")), flow)))

    return And(result)


def z3checkSat(consts, logic):
    z3Consts = z3Obj(consts)

    if logic != "NONE":
        solver = z3.SolverFor(logic)
    else:
        solver = z3.Solver()

    # solver.set("timeout", timeout * 1000)
    # target_z3_simplify = z3.simplify(z3.And(*z3Consts))
    # solver.add(target_z3_simplify)
    solver.add(z3Consts)

    with open("thermoLinear.smt2", 'w') as fle:
        print(solver.to_smt2(), file=fle)

    result = solver.check()
    str_result = str(result)
    if str_result == "sat":
        m = solver.model()
        result = False
    else:
        m = None
        result = True if str_result == "unsat" else "Unknown"
    return result, sizeAst(z3.And([z3Consts])), m


# return the size of the Z3 constraint
def sizeAst(node: z3.AstRef):
    return 1 + sum([sizeAst(c) for c in node.children()])


@singledispatch
def z3Obj(const: Constraint):
    raise NotSupportedError('Something wrong :: ' + str(const) + ":" + str(type(const)))


@z3Obj.register(RealVal)
def _(const: RealVal):
    return z3.RealVal(const.value)


@z3Obj.register(IntVal)
def _(const: IntVal):
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
    bound_str = const.start_tau.id[3:]
    new_const = And([Eq(Real("currentMode" + bound_str), RealVal(str(const.current_mode_number))),
                     make_forall_consts(const.const,
                                        const.current_mode_number,
                                        const.end_tau, const.start_tau,
                                        const.integral)])
    return z3.And(z3Obj(new_const))