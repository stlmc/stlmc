from functools import singledispatch

import z3

from stlmcPy.constraints.operations import get_vars, reverse_inequality, diff, \
    substitution_zero2t, substitution
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.assignment import Assignment, remove_prefix, get_integral
from stlmcPy.solver.abstract_solver import BaseSolver, SMTSolver
from stlmcPy.constraints.constraints import *


class Z3Solver(BaseSolver, SMTSolver):
    def __init__(self):
        self._z3_model = None

    def solve(self, all_consts, info_dict=None):
        result, size, self._z3_model = z3checkSat(all_consts, 'LRA')
        return result, size

    def simplify(self, consts):
        # substitute_list = [(z3Obj(v), z3Obj(total_dict[v])) for v in total_dict]
        # print("simplify")
        # print(substitute_list)
        # print("z3.simplify")
        # a = z3.simplify(consts)
        # print(a)
        # print(z3.substitute(a, substitute_list))
        # print(z3.get_version_string())
        # tx_0_0 = z3.Real('tx_0_0')
        # for s in substitute_list:
        #     print("=============")
        #     print("s")
        #     print(s)
        #     print("cosnts")
        #     print(consts)
        #     print(type(s[0]))
        #     print(type(s[1]))
        #     # print(a)
        #     # print(type(a))
        #     print(z3.substitute(z3.simplify(consts), s))
        #     print("=================>>>>>>>>>>>>>")
        #     print(id(get_vars(consts)))
        #     print(id(tx_0_0))
        #     print(z3.substitute(z3.simplify(consts), s))
        #     print(z3.substitute(z3.simplify(consts), (tx_0_0 >= 17 + 0, z3.BoolVal(True))))
        #     print("=============")




        # print(z3.substitute(z3.simplify(17 <= tx_0_0), (tx_0_0 >= 17 + 0, z3.BoolVal(True))))
        return z3.simplify(consts)

    def substitution(self, const, *dicts):
        total_dict = dict()
        for i in range(len(dicts)):
            total_dict.update(dicts[i])
        substitute_list = [(z3Obj(v), z3Obj(total_dict[v])) for v in total_dict]
        print(z3.simplify(z3Obj(const)))
        print("substitute_list")
        print(substitute_list)
        return z3.substitute(z3Obj(const), substitute_list)

    # def make_assignment(self, integrals_list, mode_var_dict, cont_var_dict):
    #     return Z3Assignment(self._z3_model, integrals_list, mode_var_dict, cont_var_dict)
    def make_assignment(self):
        return Z3Assignment(self._z3_model)

    def unsat_core(self, const: Constraint, assertion: list):
        solver = z3.SolverFor('LRA')
        solver.add(z3Obj(const))
        solver.check([z3Obj(c) for c in assertion])
        return solver.unsat_core()


class Z3Assignment(Assignment):
    def __init__(self, z3_model):
        self._z3_model = z3_model

    # solver_model_to_generalized_model
    def get_assignments(self):
        new_dict = dict()
        op_var_dict = {'bool': Bool, 'int': Int, 'real': Real}
        op_dict = {'bool': BoolVal, 'int': IntVal, 'real': RealVal}
        for d in self._z3_model.decls():
            var_type_str = str(d.range()).lower()
            # bound_index = d.name().find('_')
            # var_str = d.name()[0:bound_index]
            new_var = op_var_dict[var_type_str](d.name())
            z3_val = self._z3_model[d]
            new_dict[new_var] = op_dict[var_type_str](str(z3_val))
        return new_dict

    def eval(self, const):
        return self._z3_model.eval(z3Obj(const))

    # def get_assignments(self):
    #     if self._z3_model is not None:
    #         substitute_dict = self.solver_model_to_generalized_model()
    #
    #         current_mode_var_list = list()
    #         # find currentMode_i = k
    #         # i: bound info, k: mode module number
    #         for d in self._z3_model.decls():
    #             if "currentMode" in d.name():
    #                 bound_str = remove_prefix(d.name(), "currentMode_")
    #                 i = int(bound_str)
    #                 k = self._z3_model[d].as_long()
    #                 specific_integral = get_integral(self.integrals_list, i, k)
    #                 # print(specific_integral)
    #                 for exp in specific_integral.dynamics.exps:
    #                     new_exp = substitution(exp, substitute_dict)
    #                     # print(new_exp)
    #             # print("%s = %s" % (d.name(), self._z3_model[d]))
    #         # print(self._z3_model)
    #         return None
    #     return None


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

    new_forall_const = const.const
    if not isinstance(const.const, Bool):
        op_dict = {Gt: Gt, Geq: Geq, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq}
        exp = Sub(const.const.left, const.const.right)
        new_forall_child_const = reverse_inequality(op_dict[const.const.__class__](exp, RealVal('0')))
        new_forall_const = make_forall_consts(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, new_forall_child_const, const.integral))
    new_const = And([Eq(Real("currentMode" + bound_str), RealVal(str(const.current_mode_number))),
                     new_forall_const])
    return z3.And(z3Obj(new_const))
