from functools import singledispatch

import z3

from stlmcPy.constraints.operations import get_vars, reverse_inequality, diff, \
    substitution_zero2t, reduce_not, clause
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.assignment import Assignment, remove_prefix, get_integral
from stlmcPy.solver.abstract_solver import BaseSolver, SMTSolver
from stlmcPy.constraints.constraints import *
from timeit import default_timer as timer

from stlmcPy.tree.operations import size_of_tree
from stlmcPy.util.logger import Logger


class Z3Solver(SMTSolver):
    def __init__(self):
        SMTSolver.__init__(self)
        self._z3_model = None
        self._cache = list()
        self._logic_list = ["LRA", "NRA"]
        self._logic = "NRA"

    def set_logic(self, logic_name: str):
        self._logic = (logic_name.upper() if logic_name.upper() in self._logic_list else 'NRA')

    def z3checkSat(self, consts, logic):
        assert self.logger is not None
        logger = self.logger
        
        solver = z3.Solver()

        logger.start_timer("solving timer")
        solver.add(consts)

        with open("battery.smt2", 'w') as fle:
            print(solver.to_smt2(), file=fle)

        result = solver.check()
        logger.stop_timer("solving timer")
        logger.add_info("smt solving time", logger.get_duration_time("solving timer"))
        str_result = str(result)
        if str_result == "sat":
            m = solver.model()
            # print(m)
            result = False
        else:
            m = None
            result = True if str_result == "unsat" else "Unknown"
        
        return result, m

    def solve(self, all_consts=None, info_dict=None, boolean_abstract=None):
        size = 0
        if all_consts is not None:
            self._cache.append(z3Obj(all_consts))
            size = size_of_tree(all_consts)
        result, self._z3_model = self.z3checkSat(z3.And(self._cache), self._logic)
        return result, size
        # return result, -1

    def clear(self):
        self._cache = list()

    def result_simplify(self):
        return z3.simplify(z3.And(self._cache))

    def simplify(self, consts):
        return z3.simplify(consts)

    def cache(self):
        return self._cache

    def add(self, const):
        self._cache.append(z3Obj(const))

    def substitution(self, const, *dicts):
        total_dict = dict()
        for i in range(len(dicts)):
            total_dict.update(dicts[i])
        substitute_list = [(z3Obj(v), z3Obj(total_dict[v])) for v in total_dict]
        return z3.substitute(z3Obj(const), substitute_list)

    def make_assignment(self):
        return Z3Assignment(self._z3_model)

    def unsat_core(self, psi, assertion_and_trace):
        solver = z3.SolverFor('LRA')
        trace_dict = dict()
        for (assertion, trace) in assertion_and_trace:
            # trace should be boolean var
            trace_dict[str(trace.id)] = assertion
            solver.assert_and_track(z3Obj(assertion), z3Obj(trace))
        solver.add(z3Obj(Not(psi)))
        solver.check()
        unsat_cores = solver.unsat_core()
        result = set()
        for unsat_core in unsat_cores:
            result.add(trace_dict[str(unsat_core)])
        return result

    def add_contradict_consts(self):
        clause_set = set()
        for i in self._cache:
            clause_set = clause_set.union(clause(i))

        cons = set()
        for i in clause_set:
            if isinstance(i, BinaryFormula) and not isinstance(i, Implies) and not isinstance(i, Neq):
                if len(get_vars(i)) > 0:
                    cons.add(i)
        cons_list = list(cons)
        for i in range(len(cons_list)):
            cur_const = cons_list[i]
            for j in range(i+1, len(cons_list)):
                flag = False
                comp_const = cons_list[j]
                if len(get_vars(cur_const.left)) > 0:
                    if str(cur_const.left) == str(comp_const.left):
                        if isinstance(cur_const, Eq) and isinstance(comp_const, Eq):
                            if not str(cur_const.right) == str(comp_const.right):
                                flag = True
                        elif type(cur_const) in [Lt, Leq] and type(comp_const) in [Gt, Geq]:
                            if len(get_vars(cur_const.right)) == 0 and len(get_vars(comp_const.right)) == 0:
                                if int(parse_expr(infix(cur_const.right))) < int(parse_expr(infix(comp_const.right))):
                                    flag = True
                        elif type(cur_const) in [Gt, Geq] and type(comp_const) in [Lt, Leq]:
                            if len(get_vars(cur_const.right)) == 0 and len(get_vars(comp_const.right)) == 0:
                                if int(parse_expr(infix(cur_const.right))) > int(parse_expr(infix(comp_const.right))):
                                    flag = True
                    elif str(cur_const.left) == str(comp_const.right):
                        if type(cur_const) in [Lt, Leq] and type(comp_const) in [Gt, Geq]:
                            if len(get_vars(cur_const.right)) == 0 and len(get_vars(comp_const.left)) == 0:
                                if int(parse_expr(infix(cur_const.right))) < int(parse_expr(infix(comp_const.left))):
                                    flag = True
                        elif type(cur_const) in [Gt, Geq] and type(comp_const) in [Lt, Leq]:
                            if len(get_vars(cur_const.right)) == 0 and len(get_vars(comp_const.left)) == 0:
                                if int(parse_expr(infix(cur_const.right))) > int(parse_expr(infix(comp_const.left))):
                                    flag = True
                elif len(get_vars(cur_const.right)) > 0:
                    if str(cur_const.right) == str(comp_const.left):
                        if type(cur_const) in [Lt, Leq] and type(comp_const) in [Lt, Leq]:
                            if len(get_vars(cur_const.left)) == 0 and len(get_vars(comp_const.right)) == 0:
                                if int(parse_expr(infix(cur_const.left))) > int(parse_expr(infix(comp_const.right))):
                                    flag = True
                        elif type(cur_const) in [Gt, Geq] and type(comp_const) in [Gt, Geq]:
                            if len(get_vars(cur_const.left)) == 0 and len(get_vars(comp_const.right)) == 0:
                                if int(parse_expr(infix(cur_const.left))) < int(parse_expr(infix(comp_const.right))):
                                    flag = True
                    elif str(cur_const.right) == str(comp_const.right):
                        if type(cur_const) in [Lt, Leq] and type(comp_const) in [Gt, Geq]:
                            if len(get_vars(cur_const.left)) == 0 and len(get_vars(comp_const.left)) == 0:
                                if int(parse_expr(infix(cur_const.left))) > int(parse_expr(infix(comp_const.left))):
                                    flag = True
                        elif type(cur_const) in [Gt, Geq] and type(comp_const) in [Lt, Leq]:
                            if len(get_vars(cur_const.left)) == 0 and len(get_vars(comp_const.left)) == 0:
                                if int(parse_expr(infix(cur_const.left))) < int(parse_expr(infix(comp_const.left))):
                                    flag = True
                if flag:
                    self._cache.append(Or([Not(cur_const), Not(comp_const)]))


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
            new_var = op_var_dict[var_type_str](d.name())
            z3_val = self._z3_model[d]
            new_dict[new_var] = op_dict[var_type_str](str(z3_val))
        return new_dict

    def eval(self, const):
        if self._z3_model is None:
            raise NotSupportedError("Z3 has no model")
        return self._z3_model.eval(z3Obj(const))

    def z3eval(self, const):
        if self._z3_model is None:
            raise NotSupportedError("Z3 has no model")
        return self._z3_model.eval(const)


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
        if bound_str == "0":
            start_tau_var = RealVal("0")
        else:
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
    monotone_cond = Or([Geq(diff(start_forall_exp, forall.integral), RealVal('0')),
                        Leq(diff(start_forall_exp, forall.integral), RealVal('0'))])

    return And([forall.const,
                substitution_zero2t(forall.const),
                monotone_cond,
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
    bound_str = str(int(const.end_tau.id[4:]) - 1) 
    
    if len(get_vars(const.const)) == 0:
        return z3Obj(const.const)

    new_forall_const = const.const
    cur_mode = const.current_mode_number
    result = list()
    if isinstance(const.const, Bool):
        return z3Obj(const.const)
    if isinstance(const.const, Not):
        if isinstance(const.const.child, Bool):
            return z3.Not(z3Obj(const.const.child))
        if isinstance(const.const.child, Not):
            return z3Obj(const.const.child.child)
        reduced_const = reduce_not(const.const)
        new_const = z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, reduced_const, const.integral))
        return new_const
    elif isinstance(const.const, Implies):
        left = reduce_not(Not(const.const.left))
        right = const.const.right
        left_new = z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, left, const.integral))
        right_new = z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, right, const.integral))
        return z3.Or([left_new, right_new])
    elif isinstance(const.const, And) or isinstance(const.const, Or):
        op_dict = {And: z3.And, Or: z3.Or}
        result = list()
        for c in const.const.children:
            if isinstance(c, Bool):
                result.append(z3Obj(c))
            elif get_vars(c) is None:
                result.append(z3Obj(c))
            else:
                result.append(z3Obj(Forall(const.current_mode_number, const.end_tau, const.start_tau, c, const.integral)))
        return op_dict[const.const.__class__](result)
    elif not isinstance(const.const, Bool):
        op_dict = {Gt: Gt, Geq: Geq, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq}
        exp = Sub(const.const.left, const.const.right)
        new_forall_child_const = reverse_inequality(op_dict[const.const.__class__](exp, RealVal('0')))
        new_forall_const = make_forall_consts(
            Forall(const.current_mode_number, const.end_tau, const.start_tau, new_forall_child_const, const.integral))
    new_const = And([Eq(Real("currentMode_" + bound_str), RealVal(str(const.current_mode_number))),
                     new_forall_const])
    
    return z3.And(z3Obj(new_const))
