from functools import singledispatch

from .constraints import *
from ..exception.exception import NotSupportedError
from itertools import combinations


@singledispatch
def substitution(const: Constraint, substitution_dict):
    return const


@substitution.register(Variable)
def _(const: Variable, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return const


@substitution.register(Add)
def _(const: Add, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Add(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Sub)
def _(const: Sub, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Sub(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Mul)
def _(const: Mul, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Mul(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Div)
def _(const: Div, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Div(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Pow)
def _(const: Pow, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Pow(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Neg)
def _(const: Neg, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Neg(substitution(const.child, substitution_dict))


@substitution.register(Function)
def _(const: Function, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Function([substitution(var, substitution_dict) for var in const.vars],
                    [substitution(exp, substitution_dict) for exp in const.exps])


@substitution.register(Ode)
def _(const: Ode, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Ode([substitution(var, substitution_dict) for var in const.vars],
               [substitution(exp, substitution_dict) for exp in const.exps])


@substitution.register(And)
def _(const: And, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    children = list()
    for child in const.children:
        children.append(substitution(child, substitution_dict))
    return And(children)


@substitution.register(Or)
def _(const: Or, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    children = list()
    for child in const.children:
        children.append(substitution(child, substitution_dict))
    return Or(children)


@substitution.register(Not)
def _(const: Not, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Not(substitution(const.child, substitution_dict))


@substitution.register(Gt)
def _(const: Gt, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Gt(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict), const.is_range)


@substitution.register(Geq)
def _(const: Geq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Geq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict), const.is_range)


@substitution.register(Lt)
def _(const: Lt, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Lt(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict), const.is_range)


@substitution.register(Leq)
def _(const: Leq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Leq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict), const.is_range)


@substitution.register(Eq)
def _(const: Eq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Eq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict), const.is_range)


@substitution.register(Neq)
def _(const: Neq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Neq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Implies)
def _(const: Implies, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Implies(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Forall)
def _(const: Forall, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Forall(const.current_mode_number, const.end_tau, const.start_tau,
                  substitution(const.const, substitution_dict), const.integral)


@substitution.register(FinallyFormula)
def _(const: FinallyFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return FinallyFormula(const.local_time, const.global_time, substitution(const.child, substitution_dict))


@substitution.register(GloballyFormula)
def _(const: GloballyFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return GloballyFormula(const.local_time, const.global_time, substitution(const.child, substitution_dict))


@substitution.register(UntilFormula)
def _(const: UntilFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return UntilFormula(const.local_time, const.global_time,
                        substitution(const.left, substitution_dict),
                        substitution(const.right, substitution_dict))


@substitution.register(ReleaseFormula)
def _(const: ReleaseFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return ReleaseFormula(const.local_time, const.global_time,
                          substitution(const.left, substitution_dict),
                          substitution(const.right, substitution_dict))


# mode_dict => key : string, value : object
# cont_dict => key : object, value : (left_end, left, right, right_end)
# assumption : object is variable type
def make_dict(bound, mode_dict, cont_dict, constant_dict, suffix=""):
    result_dict = dict()
    op_dict = {'bool': Bool, 'int': Int, 'real': Real}
    for key in mode_dict:
        mode_var = mode_dict[key]
        var_type = mode_var.type
        result_dict[mode_dict[key]] = op_dict[var_type](mode_var.id + "_" + str(bound))

    for cont_var in cont_dict:
        result_dict[cont_var] = Real(cont_var.id + "_" + str(bound) + suffix)

    for const_var in constant_dict:
        result_dict[const_var] = constant_dict[const_var]

    return result_dict


@singledispatch
def make_dictionary_for_invariant(cur_inv_const: Formula, inv_prop_dict: dict):
    return cur_inv_const, inv_prop_dict


@make_dictionary_for_invariant.register(And)
def _(cur_inv_const: And, inv_prop_dict: dict):
    new_child = list()
    for const in cur_inv_const.children:
        formula, new_dict = make_dictionary_for_invariant(const, inv_prop_dict)
        new_child.append(formula)
        inv_prop_dict.update(new_dict)
    return And(new_child), inv_prop_dict


@make_dictionary_for_invariant.register(Or)
def _(cur_inv_const: Or, inv_prop_dict: dict):
    new_child = list()
    for const in cur_inv_const.children:
        formula, new_dict = make_dictionary_for_invariant(const, inv_prop_dict)
        new_child.append(formula)
        inv_prop_dict.update(new_dict)
    return Or(new_child), inv_prop_dict


# assumption: there will be no BinaryTemporalFormula fot cur_inv_const
@make_dictionary_for_invariant.register(BinaryFormula)
def _(cur_inv_const: BinaryFormula, inv_prop_dict: dict):
    index = len(inv_prop_dict) + 1
    new_id = "invAtomicID_" + str(index)
    new_var = Bool(new_id)
    inv_prop_dict[new_var] = cur_inv_const
    return new_var, inv_prop_dict


def get_max_bound(literal):
    max_bound = 0
    bound = -1
    for v in get_vars(literal):
        if isinstance(v, Bool):
            index = int(v.id.rfind("_")) + 1
            bound = int(v.id[index:])
            if max_bound < bound:
                max_bound = bound
        else:
            s_index = int(v.id.find("_"))
            e_index = int(v.id.rfind("_"))
            if s_index == e_index:
                bound = int(v.id[s_index + 1:]) - 1
            else:
                # if "_0_0" in v.id or "_t" in v.id:
                bound = int(v.id[s_index + 1:e_index])
            if max_bound < bound:
                max_bound = bound
    return max_bound


@singledispatch
def get_vars(const: Constraint):
    return set()


@get_vars.register(Unary)
def _(const: Unary):
    return get_vars(const.child)


@get_vars.register(Binary)
def _(const: Binary):
    left = get_vars(const.left)
    right = get_vars(const.right)
    return left.union(right)


@get_vars.register(Multinary)
def _(const: Multinary):
    result = set()
    for c in const.children:
        result = result.union(get_vars(c))
    return result


@get_vars.register(Variable)
def _(const: Variable):
    return {const}


@get_vars.register(Integral)
def _(const: Integral):
    result = set()
    for ev in const.end_vector:
        result.add(ev)
    for sv in const.start_vector:
        result.add(sv)
    result.add(const)
    return result


@get_vars.register(Forall)
def _(const: Forall):
    return get_vars(const.const)


@singledispatch
def relaxing(const: Formula, delta: float):
    return const


@relaxing.register(And)
def _(const: And, delta: float):
    return And([relaxing(c, delta) for c in const.children])


@relaxing.register(Or)
def _(const: Or, delta: float):
    return Or([relaxing(c, delta) for c in const.children])


@relaxing.register(Not)
def _(const: Not, delta: float):
    return Not(relaxing(const.child, delta))


@relaxing.register(Implies)
def _(const: Implies, delta: float):
    return Implies(relaxing(const.left, delta), relaxing(const.right, delta))


@relaxing.register(Geq)
def _(const: Geq, delta: float):
    return Geq(const.left, Sub(const.right, RealVal(str(delta))))


@relaxing.register(Gt)
def _(const: Gt, delta: float):
    return Geq(const.left, Sub(const.right, RealVal(str(delta))))


@relaxing.register(Leq)
def _(const: Leq, delta: float):
    return Leq(const.left, Add(const.right, RealVal(str(delta))))


@relaxing.register(Lt)
def _(const: Lt, delta: float):
    return Leq(const.left, Add(const.right, RealVal(str(delta))))


@relaxing.register(Eq)
def _(const: Eq, delta: float):
    if isinstance(const.left, Bool) or isinstance(const.right, Bool):
        return const
    return And([Geq(const.left, Sub(const.right, Div(RealVal(str(delta)), RealVal('2')))),
                Leq(const.left, Add(const.right, Div(RealVal(str(delta)), RealVal('2'))))])


@relaxing.register(Neq)
def _(const: Neq, delta: float):
    if isinstance(const.left, Bool) or isinstance(const.right, Bool):
        return const
    return Or([Leq(const.left, Sub(const.right, Div(RealVal(str(delta)), RealVal('2')))),
               Geq(const.left, Add(const.right, Div(RealVal(str(delta)), RealVal('2'))))])


@relaxing.register(BinaryTemporalFormula)
def _(const: BinaryTemporalFormula, delta: float):
    return const.__class__(const.local_time, const.global_time, relaxing(const.left, delta),
                           relaxing(const.right, delta))


@relaxing.register(UnaryTemporalFormula)
def _(const: UnaryTemporalFormula, delta: float):
    return const.__class__(const.local_time, const.global_time, relaxing(const.child, delta))


@singledispatch
def reverse_inequality(const: Constraint):
    return const


@reverse_inequality.register(Lt)
def _(const):
    return Gt(Neg(const.left), Neg(const.right))


@reverse_inequality.register(Leq)
def _(const):
    return Geq(Neg(const.left), Neg(const.right))


def diff(exp: Expr, integral: Integral):
    alpha = make_diff_mapping(integral)
    new_exp = substitution(exp, alpha)

    return diff_aux(new_exp)


def make_diff_mapping(integral: Integral):
    new_dict = dict()
    index = 0
    for dyn_var in integral.start_vector:
        if not isinstance(integral.dynamics, Ode):
            new_dict[dyn_var] = integral.dynamics.exps[index]
        else:
            one_var = integral.end_vector[0].id
            bound_start = one_var.find("_") + 1
            bound_end = one_var.rfind("_")
            cur_bound = one_var[bound_start:bound_end]
            cur_dur_start = Real("tau_" + cur_bound)
            if cur_bound == "0":
                cur_dur_start = RealVal("0")
            cur_dur_end = Real("tau_" + str(int(cur_bound) + 1))
            # new_dict[dyn_var] = Mul(integral.dynamics.exps[index], (cur_dur_end - cur_dur_start))
            new_dict[dyn_var] = Mul(integral.dynamics.exps[index], cur_dur_end)
        index += 1
    return new_dict


@singledispatch
def diff_aux(const: Constraint):
    raise NotImplementedError('Something wrong')


@diff_aux.register(Constant)
def _(const):
    return RealVal("0")


@diff_aux.register(Variable)
def _(const):
    if str(const.id)[0:3] == 'tau':
        return RealVal("1")
    else:
        return RealVal("0")


@diff_aux.register(Add)
def _(const):
    x = const.left
    y = const.right

    if get_vars(const) is None:
        return RealVal("0")
    if get_vars(x) is None:
        return diff_aux(y)
    if get_vars(y) is None:
        return diff_aux(x)

    return Add(diff_aux(x), diff_aux(y))


@diff_aux.register(Sub)
def _(const):
    x = const.left
    y = const.right

    if get_vars(const) is None:
        return RealVal("0")
    if get_vars(x) is None:
        return diff_aux(y)
    if get_vars(y) is None:
        return diff_aux(x)

    return Sub(diff_aux(x), diff_aux(y))


@diff_aux.register(Pow)
def _(const):
    x = const.left
    y = const.right

    if isinstance(x, Variable) and (len(get_vars(y)) == 0):
        if eval(str(infix(y))) == 0:
            return RealVal("0")
        elif str(x.id)[0:3] == 'tau':
            return Mul(y, Pow(x, (Sub(y, RealVal("1")))))
        else:
            return RealVal("0")
    else:
        raise NotSupportedError('Cannot handling polynomial yet : {}'.format(const))


@diff_aux.register(Mul)
def _(const):
    x = const.left
    y = const.right

    if len(get_vars(const)) == 0:
        return RealVal("0")
    if len(get_vars(x)) == 0:
        return Mul(x, diff_aux(y))
    if len(get_vars(y)) == 0:
        return Mul(diff_aux(x), y)

    return Add(Mul(diff_aux(x), y), Mul(x, diff_aux(y)))


@diff_aux.register(Div)
def _(const):
    x = const.left
    y = const.right
    if len(get_vars(const)) == 0:
        return RealVal("0")
    if len(get_vars(x)) == 0:
        return Sub(RealVal("0"), Div(Mul(diff_aux(y), x), Mul(y, y)))
    if len(get_vars(y)) == 0:
        return Div(diff_aux(x), y)

    return Sub(Div(diff_aux(x), y), Div(Mul(diff_aux(y), x), Mul(y, y)))


@diff_aux.register(Neg)
def _(const):
    x = diff_aux(const.child)
    return Neg(x)


@singledispatch
def substitution_zero2t(const: Constraint):
    return const


@substitution_zero2t.register(Neg)
def _(const):
    return Neg(substitution_zero2t(const.child))


@substitution_zero2t.register(Not)
def _(const):
    return Not(substitution_zero2t(const.child))


@substitution_zero2t.register(Binary)
def _(const: Binary):
    op_dict = {Geq: Geq, Gt: Gt, Lt: Lt, Leq: Leq, Eq: Eq, Neq: Neq,
               Add: Add, Sub: Sub, Div: Div, Mul: Mul, Pow: Pow}
    return op_dict[const.__class__](substitution_zero2t(const.left), substitution_zero2t(const.right))


@substitution_zero2t.register(And)
def _(const: And):
    return And([substitution_zero2t(c) for c in const.children])


@substitution_zero2t.register(Or)
def _(const: Or):
    return Or([substitution_zero2t(c) for c in const.children])


@substitution_zero2t.register(Variable)
def _(const: Variable):
    op_dict = {Bool: Bool, Real: Real, Int: Int}
    if (not const.id.find("_") == const.id.rfind("_")) and const.id[-2:] == "_0":
        return op_dict[const.__class__](const.id[:-2] + "_t")
    return const


@singledispatch
def reduce_not(const: Constraint):
    return const


@reduce_not.register(Not)
def _(const: Not):
    child = const.child
    if isinstance(child, Lt):
        return Geq(child.left, child.right)
    if isinstance(const.child, Gt):
        return Leq(child.left, child.right)
    if isinstance(child, Leq):
        return Gt(child.left, child.right)
    if isinstance(child, Geq):
        return Lt(child.left, child.right)
    if isinstance(child, Eq):
        return Neq(child.left, child.right)
    if isinstance(child, Neq):
        return Eq(child.left, child.right)
    if isinstance(child, Constant):
        if child.value == 'True':
            return BoolVal('False')
        elif child.value == 'False':
            return BoolVal('True')
        else:
            raise NotSupportedError("think wise real or integer type cannot be negated")
    if isinstance(child, And):
        return Or([reduce_not(Not(c)) for c in child.children])
    if isinstance(child, Or):
        return And([reduce_not(Not(c)) for c in child.children])
    if isinstance(child, Implies):
        return And([reduce_not(child.left), reduce_not(Not(child.right))])
    if isinstance(child, FinallyFormula):
        return GloballyFormula(child.local_time, child.global_time, reduce_not(Not(child.child)))
    if isinstance(child, GloballyFormula):
        return FinallyFormula(child.local_time, child.global_time, reduce_not(Not(child.child)))
    if isinstance(child, UntilFormula):
        return ReleaseFormula(child.local_time, child.global_time,
                              reduce_not(Not(child.left)),
                              reduce_not(Not(child.right)))
    if isinstance(child, ReleaseFormula):
        return UntilFormula(child.local_time, child.global_time,
                            reduce_not(Not(child.left)),
                            reduce_not(Not(child.right)))
    if isinstance(child, Not):
        return child.child
    if isinstance(child, Bool):
        return Bool("not@" + child.id)
    return const


@reduce_not.register(And)
def _(const: And):
    return And([reduce_not(c) for c in const.children])


@reduce_not.register(Or)
def _(const: Or):
    return Or([reduce_not(c) for c in const.children])


@reduce_not.register(Implies)
def _(const: Implies):
    return Implies(reduce_not(const.left), reduce_not(const.right))


@reduce_not.register(Eq)
def _(const: Eq):
    return Eq(reduce_not(const.left), reduce_not(const.right))


@reduce_not.register(Neq)
def _(const: Neq):
    return Neq(reduce_not(const.left), reduce_not(const.right))


@reduce_not.register(FinallyFormula)
def _(const: FinallyFormula):
    return FinallyFormula(const.local_time, const.global_time, reduce_not(const.child))


@reduce_not.register(GloballyFormula)
def _(const: GloballyFormula):
    return GloballyFormula(const.local_time, const.global_time, reduce_not(const.child))


@reduce_not.register(UntilFormula)
def _(const: UntilFormula):
    return UntilFormula(const.local_time, const.global_time,
                        reduce_not(const.left),
                        reduce_not(const.right))


@reduce_not.register(ReleaseFormula)
def _(const: ReleaseFormula):
    return ReleaseFormula(const.local_time, const.global_time,
                          reduce_not(const.left),
                          reduce_not(const.right))


@singledispatch
def bound_tau_max(const: Constraint, tb):
    return const


@bound_tau_max.register(And)
def _(const: And, tb):
    return And([bound_tau_max(c, tb) for c in const.children])


@bound_tau_max.register(Or)
def _(const: Or, tb):
    return Or([bound_tau_max(c, tb) for c in const.children])


@bound_tau_max.register(Implies)
def _(const: Implies, tb):
    return Implies(bound_tau_max(const.left, tb), bound_tau_max(const.right, tb))


@bound_tau_max.register(Eq)
def _(const: Eq, tb):
    return Eq(bound_tau_max(const.left, tb), bound_tau_max(const.right, tb))


@bound_tau_max.register(Neq)
def _(const: Neq, tb):
    return Neq(bound_tau_max(const.left, tb), bound_tau_max(const.right, tb))


@bound_tau_max.register(FinallyFormula)
def _(const: FinallyFormula, tb):
    gt = const.global_time
    bound_interval = Interval(gt.left_end, gt.left, True, RealVal(str(tb)))

    return FinallyFormula(const.local_time, bound_interval, bound_tau_max(const.child, tb))


@bound_tau_max.register(GloballyFormula)
def _(const: GloballyFormula, tb):
    gt = const.global_time
    bound_interval = Interval(gt.left_end, gt.left, True, RealVal(str(tb)))
    return GloballyFormula(const.local_time, bound_interval, bound_tau_max(const.child, tb))


@bound_tau_max.register(UntilFormula)
def _(const: UntilFormula, tb):
    gt = const.global_time
    bound_interval = Interval(gt.left_end, gt.left, True, RealVal(str(tb)))
    return UntilFormula(const.local_time, bound_interval,
                        bound_tau_max(const.left, tb),
                        bound_tau_max(const.right, tb))


@bound_tau_max.register(ReleaseFormula)
def _(const: ReleaseFormula, tb):
    gt = const.global_time
    bound_interval = Interval(gt.left_end, gt.left, True, RealVal(str(tb)))
    return And([ReleaseFormula(const.local_time, bound_interval,
                               bound_tau_max(const.left, tb),
                               bound_tau_max(const.right, tb)),
                FinallyFormula(Interval(True, RealVal('0'), False, RealVal('inf')), bound_interval,
                               bound_tau_max(const.left, tb))])


@singledispatch
def get_boolean_abstraction(const: Constraint):
    return set()


@get_boolean_abstraction.register(Forall)
def _(const: Forall):
    return {const}


@get_boolean_abstraction.register(Integral)
def _(const: Integral):
    return {const}


@get_boolean_abstraction.register(Unary)
def _(const: Unary):
    return get_boolean_abstraction(const.child)


@get_boolean_abstraction.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Forall) or isinstance(const.right, Forall):
        return {const}
    elif isinstance(const.left, Bool):
        if "newTau#" in const.left.id:
            return {const}
        return set()
    else:
        return set()


@get_boolean_abstraction.register(Binary)
def _(const: Binary):
    left_set = get_boolean_abstraction(const.left)
    right_set = get_boolean_abstraction(const.right)
    return left_set.union(right_set)


@get_boolean_abstraction.register(Multinary)
def _(const: Multinary):
    new_set = set()
    for c in const.children:
        new_set = new_set.union(get_boolean_abstraction(c))
    return new_set


@singledispatch
def forall_integral_substitution(const: Constraint, substitution_dict):
    return const


@forall_integral_substitution.register(And)
def _(const: And, substitution_dict):
    children = list()
    for child in const.children:
        children.append(forall_integral_substitution(child, substitution_dict))
    return And(children)


@forall_integral_substitution.register(Or)
def _(const: Or, substitution_dict):
    children = list()
    for child in const.children:
        children.append(forall_integral_substitution(child, substitution_dict))
    return Or(children)


@forall_integral_substitution.register(Not)
def _(const: Not, substitution_dict):
    return Not(forall_integral_substitution(const.child, substitution_dict))


@forall_integral_substitution.register(Eq)
def _(const: Eq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return const


@forall_integral_substitution.register(Neq)
def _(const: Neq, substitution_dict):
    return Neq(forall_integral_substitution(const.left, substitution_dict),
               forall_integral_substitution(const.right, substitution_dict))


@forall_integral_substitution.register(Implies)
def _(const: Implies, substitution_dict):
    return Implies(forall_integral_substitution(const.left, substitution_dict),
                   forall_integral_substitution(const.right, substitution_dict))


@forall_integral_substitution.register(Forall)
def _(const: Forall, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return const


@forall_integral_substitution.register(Integral)
def _(const: Integral, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return const


def inverse_dict(original_dict: dict):
    new_dict = dict()
    for key in original_dict:
        new_dict[original_dict[key]] = key
    return new_dict


def generate_id(initial, gid='v'):
    counter = initial
    while True:
        yield gid + str(counter)
        counter += 1


def make_boolean_abstract_consts(props: dict):
    result = list()
    all_vars_list = props.keys()
    all_vars_list = sorted(all_vars_list, key=lambda x: x.id)
    for p in all_vars_list:
        result.append(Eq(p, props[p]))
    return And(result)


@singledispatch
def infix(const: Constraint):
    return str(const)


@infix.register(Variable)
def _(const: Variable):
    return const.id


@infix.register(And)
def _(const: And):
    return '&'.join([infix(c) for c in const.children])


@infix.register(Geq)
def _(const: Geq):
    return infix(const.left) + " >= " + infix(const.right)


@infix.register(Gt)
def _(const: Geq):
    return infix(const.left) + " >= " + infix(const.right)


@infix.register(Leq)
def _(const: Geq):
    return infix(const.left) + " <= " + infix(const.right)


@infix.register(Lt)
def _(const: Geq):
    return infix(const.left) + " <= " + infix(const.right)


@infix.register(Eq)
def _(const: Eq):
    return infix(const.left) + " >= " + infix(const.right) + " & " + infix(const.left) + " <= " + infix(
        const.right)


@infix.register(Neq)
def _(const: Geq):
    return infix(const.left) + " >= " + infix(const.right) + " & " + infix(const.left) + " < " + infix(
        const.right)


@infix.register(Add)
def _(const: Add):
    return "(" + infix(const.left) + " + " + infix(const.right) + ")"


@infix.register(Sub)
def _(const: Sub):
    return "(" + infix(const.left) + " - " + infix(const.right) + ")"


@infix.register(Neg)
def _(const: Neg):
    return "(-" + infix(const.child) + ")"


@infix.register(Mul)
def _(const: Mul):
    return "(" + infix(const.left) + " * " + infix(const.right) + ")"


@infix.register(Div)
def _(const: Div):
    return "(" + infix(const.left) + " / " + infix(const.right) + ")"


@infix.register(Pow)
def _(const: Pow):
    return "(" + infix(const.left) + " ** " + infix(const.right) + ")"


@infix.register(Forall)
def _(const: Forall):
    return infix(const.const)


@singledispatch
def make_new_dynamics(dyn: Ode, bound, mode_var_dict, range_dict, constant_dict):
    new_dynamics_dict = make_dict(bound, mode_var_dict, range_dict, constant_dict, "_0")
    new_dynamics_dict[Real('time')] = Real('tau_' + str(bound + 1))
    new_exps = list()
    for exp in dyn.exps:
        new_exp = substitution(exp, new_dynamics_dict)
        new_exps.append(new_exp)

    new_vars_dict = make_dict(bound, {}, range_dict, {}, "_0_t")
    new_vars = list()
    for var in dyn.vars:
        new_var = substitution(var, new_vars_dict)
        new_vars.append(new_var)
    return Ode(new_vars, new_exps)


@make_new_dynamics.register(Function)
def _(dyn: Function, bound, mode_var_dict, range_dict, constant_dict):
    new_dynamics_dict = make_dict(bound, mode_var_dict, range_dict, constant_dict, "_0")
    new_dynamics_dict[Real('time')] = Real('tau_' + str(bound + 1)) - Real('tau_' + str(bound))
    new_exps = list()
    for exp in dyn.exps:
        new_exp = substitution(exp, new_dynamics_dict)
        new_exps.append(new_exp)

    new_vars_dict = make_dict(bound, {}, range_dict, {}, "_0_t")
    new_vars = list()
    for var in dyn.vars:
        new_var = substitution(var, new_vars_dict)
        new_vars.append(new_var)
    return Function(new_vars, new_exps)


@singledispatch
def clause(const: Constraint):
    return {const}


@clause.register(Not)
def _(const: Not):
    return clause(const.child)


@clause.register(And)
def _(const: And):
    result = set()
    for c in list(const.children):
        result = result.union(clause(c))
    return result


@clause.register(Eq)
def _(const: Eq):
    if isinstance(const.left, Formula):
        return clause(const.left).union(clause(const.right))
    return {const}


@clause.register(Or)
def _(const: Or):
    result = set()
    for c in list(const.children):
        result = result.union(clause(c))
    return result


@clause.register(Not)
def _(const: Not):
    result = set()
    return result.union(clause(const.child))


@clause.register(Implies)
def _(const):
    result = set()
    result = result.union(clause(const.left))
    result = result.union(clause(const.right))
    return result


@clause.register(FinallyFormula)
def _(const):
    return clause(const.child)


@clause.register(GloballyFormula)
def _(const):
    return clause(const.child)


@clause.register(UntilFormula)
def _(const):
    result = set()
    result = result.union(clause(const.left))
    result = result.union(clause(const.right))
    return result


@clause.register(ReleaseFormula)
def _(const):
    result = set()
    result = result.union(clause(const.left))
    result = result.union(clause(const.right))
    return result


def lower_encoding(chi, bound, lower):
    com_list = [(chi + "_" + str(i), chi + "_" + str(i + 1)) for i in range(1, 2 * (bound + 1))]
    combi = combinations(com_list, lower)
    result = list()
    for i in combi:
        rest = com_list[:]
        sub = list()
        for j in i:
            rest.remove(j)
            sub.append(Neq(Bool(j[0]), Bool(j[1])))
        for j in rest:
            sub.append(Eq(Bool(j[0]), Bool(j[1])))
        result.append(And(sub))
    return Or(result)


def get_max_depth(const: Constraint):
    queue = list()
    waiting_queue = list()

    waiting_queue.append(const)
    queue.append((0, const, None))
    level = 0
    while len(waiting_queue) > 0:
        n = waiting_queue.pop(0)
        if isinstance(n, NonLeaf):
            level += 1
            for c in n.children:
                waiting_queue.append(c)
                queue.append((level, c, n))

    max_depth = 0
    while len(queue) > 0:
        n, node, p = queue.pop(0)
        if n > max_depth:
            max_depth = n
        # print("depth: {}, {} ({}) :: parent {}\n".format(n, node, id(node), id(p)))
    return max_depth


def fresh_new_var():
    new_var = Bool("")
    new_var.id = "opt_var_{}".format(id(new_var))
    return new_var


def is_proposition(constraint: Constraint):
    if isinstance(constraint, Bool):
        return True
    else:
        if not isinstance(constraint, Variable) and isinstance(constraint, Leaf):
            return True
    return False


def subformula(formula: Formula) -> set:
    assert isinstance(formula, Formula)
    set_of_formulas = set()
    count = 0

    # first children
    root = (count, formula)

    waiting_queue = set()
    waiting_queue.add(root)
    set_of_formulas.add(formula)

    while len(waiting_queue) > 0:
        count = count + 1
        _, f = waiting_queue.pop()

        if is_proposition(f):
            set_of_formulas.add(f)
        elif isinstance(f, UnaryFormula):
            set_of_formulas.add(f)
            waiting_queue.add((count, f.child))
        elif isinstance(f, BinaryFormula):
            set_of_formulas.add(f)
            waiting_queue.add((count, f.left))
            waiting_queue.add((count, f.right))
        elif isinstance(f, MultinaryFormula):
            set_of_formulas.add(f)
            for child in f.children:
                waiting_queue.add((count, child))
        else:
            continue
    return set_of_formulas


@singledispatch
def remove_binary(f: Formula):
    return f


@remove_binary.register(Not)
def _(f: Not):
    return Not(remove_binary(f.child))


@remove_binary.register(And)
def _(f: And):
    return And([remove_binary(c) for c in f.children])


@remove_binary.register(Or)
def _(f: Or):
    return Or([remove_binary(c) for c in f.children])


@remove_binary.register(Implies)
def _(f: Implies):
    return Implies(remove_binary(f.left), remove_binary(f.right))


@remove_binary.register(FinallyFormula)
def _(f: FinallyFormula):
    return FinallyFormula(f.local_time, f.global_time, remove_binary(f.child))


@remove_binary.register(GloballyFormula)
def _(f: GloballyFormula):
    return GloballyFormula(f.local_time, f.global_time, remove_binary(f.child))


@remove_binary.register(UntilFormula)
def _(f: UntilFormula):
    universeInterval = Interval(True, RealVal("0.0"), False, RealVal('inf'))
    if f.local_time == universeInterval:
        return f

    left_interval = f.local_time.left_end
    left_time = f.local_time.left
    right_interval = f.local_time.right_end
    right_time = f.local_time.right

    right = remove_binary(f.right)
    left = remove_binary(f.left)

    right_formula = FinallyFormula(Interval(left_interval, left_time, right_interval, right_time), f.global_time, right)

    if left_interval:
        left_formula_1 = GloballyFormula(Interval(False, RealVal("0"), False, left_time), f.global_time, left)
        subFormula = Or([right, And([left, UntilFormula(universeInterval, f.global_time, left, right)])])
        left_formula_2 = GloballyFormula(Interval(False, RealVal("0"), True, left_time), f.global_time, subFormula)
        return And([left_formula_1, left_formula_2, right_formula])
    else:
        subFormula = And([left, UntilFormula(universeInterval, f.global_time, left, right)])
        final_left = GloballyFormula(Interval(False, RealVal("0"), True, left_time), f.global_time, subFormula)
        return And([final_left, right_formula])


@remove_binary.register(ReleaseFormula)
def _(f: ReleaseFormula):
    universeInterval = Interval(True, RealVal("0.0"), False, RealVal('inf'))
    if f.local_time == universeInterval:
        return f

    left_interval = f.local_time.left_end
    left_time = f.local_time.left
    right_interval = f.local_time.right_end
    right_time = f.local_time.right

    right = remove_binary(f.right)
    left = remove_binary(f.left)

    right_formula = GloballyFormula(Interval(left_interval, left_time, right_interval, right_time), f.global_time,
                                    right)

    if left_interval:
        left_formula_1 = FinallyFormula(Interval(False, RealVal("0"), False, left_time), f.global_time, left)
        subFormula = And([right, Or([left, ReleaseFormula(universeInterval, f.global_time, left, right)])])
        left_formula_2 = FinallyFormula(Interval(False, RealVal("0"), True, left_time), f.global_time, subFormula)
        return Or([left_formula_1, left_formula_2, right_formula])
    else:
        subFormula = Or([left, ReleaseFormula(universeInterval, f.global_time, left, right)])
        final_left = FinallyFormula(Interval(False, RealVal("0"), True, left_time), f.global_time, subFormula)
        return Or([final_left, right_formula])
