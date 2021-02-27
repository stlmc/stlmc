from functools import singledispatch
from stlmcPy.constraints.constraints import *
from stlmcPy.exception.exception import NotSupportedError
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
    return Gt(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Geq)
def _(const: Geq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Geq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Lt)
def _(const: Lt, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Lt(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Leq)
def _(const: Leq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Leq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Eq)
def _(const: Eq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Eq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


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
    max_bound = -1
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
def relaxing(const: Formula, delta):
    return const


@relaxing.register(And)
def _(const: And, delta):
    return And([relaxing(c, delta) for c in const.children])


@relaxing.register(Or)
def _(const: Or, delta):
    return Or([relaxing(c, delta) for c in const.children])


@relaxing.register(Not)
def _(const: Not, delta):
    return Not(relaxing(const.child, delta))


@relaxing.register(Implies)
def _(const: Implies, delta):
    return Implies(relaxing(const.left, delta), relaxing(const.right, delta))


@relaxing.register(Geq)
def _(const: Geq, delta):
    return Geq(const.left, Sub(const.right, delta))


@relaxing.register(Gt)
def _(const: Gt, delta):
    return Geq(const.left, Sub(const.right, delta))


@relaxing.register(Leq)
def _(const: Leq, delta):
    return Leq(const.left, Add(const.right, delta))


@relaxing.register(Lt)
def _(const: Lt, delta):
    return Leq(const.left, Add(const.right, delta))


@relaxing.register(Eq)
def _(const: Eq, delta):
    if isinstance(const.left, Bool) or isinstance(const.right, Bool):
        return const
    return And([Geq(const.left, Sub(const.right, Div(delta, RealVal('2')))),
                Leq(const.left, Add(const.right, Div(delta, RealVal('2'))))])


@relaxing.register(Neq)
def _(const: Neq, delta):
    return Not(relaxing(Eq(const.left, const.right), delta))


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


@clause.register(Neq)
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


def update_dynamics_with_replacement(dynamics: Dynamics, v: Variable, e: Expr):
    is_update = False
    for i, dyn_var in enumerate(dynamics.vars):
        if dyn_var.id == v.id:
            dynamics.exps[i] = e
            is_update = True
    if not is_update:
        dynamics.vars.append(v)
        dynamics.exps.append(e)


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


@singledispatch
def expr_syntatic_equality(left: Expr, right: Expr):
    raise NotSupportedError("not enough information to determine equality between {} and {}".format(left, right))


@expr_syntatic_equality.register(Variable)
def _(left: Variable, right: Variable):
    if not isinstance(left, Variable) or not isinstance(right, Variable):
        return False
    return left.id == right.id


@expr_syntatic_equality.register(Constant)
def _(left: Constant, right: Constant):
    if not isinstance(left, Constant) or not isinstance(right, Constant):
        return False
    return left.value == right.value


@expr_syntatic_equality.register(BinaryExpr)
def _(left: BinaryExpr, right: BinaryExpr):
    if not ((isinstance(left, Add) and isinstance(right, Add)) or
            (isinstance(left, Sub) and isinstance(right, Sub)) or
            (isinstance(left, Mul) and isinstance(right, Mul)) or
            (isinstance(left, Div) and isinstance(right, Div)) or
            (isinstance(left, Pow) and isinstance(right, Pow))):
        return False
    return (expr_syntatic_equality(left.get_left(), right.get_left()) and expr_syntatic_equality(left.get_right(),
                                                                                                 right.get_right())) \
           or (expr_syntatic_equality(left.get_left(), right.get_right()) and expr_syntatic_equality(left.get_right(),
                                                                                                     right.get_left())) \
           or (expr_syntatic_equality(left.get_right(), right.get_left()) and expr_syntatic_equality(left.get_left(),
                                                                                                     right.get_right())) \
           or (expr_syntatic_equality(left.get_right(), right.get_right()) and expr_syntatic_equality(left.get_left(),
                                                                                                      right.get_left()))


@expr_syntatic_equality.register(UnaryExpr)
def _(left: UnaryExpr, right: UnaryExpr):
    if not ((isinstance(left, Neg) and isinstance(right, Neg)) or
            (isinstance(left, Sqrt) and isinstance(right, Sqrt)) or
            (isinstance(left, Sin) and isinstance(right, Sin)) or
            (isinstance(left, Cos) and isinstance(right, Cos)) or
            (isinstance(left, Arcsin) and isinstance(right, Arcsin)) or
            (isinstance(left, Arccos) and isinstance(right, Arccos)) or
            (isinstance(left, Arctan) and isinstance(right, Arctan))):
        return False
    return (expr_syntatic_equality(left.child, right.child) and expr_syntatic_equality(left.child, right.child)) \
           or (expr_syntatic_equality(left.child, right.child) and expr_syntatic_equality(left.child, right.child)) \
           or (expr_syntatic_equality(left.child, right.child) and expr_syntatic_equality(left.child, right.child)) \
           or (expr_syntatic_equality(left.child, right.child) and expr_syntatic_equality(left.child, right.child))


def expr_syntatic_equality_linear(left: Expr, right: Expr):
    def _get_type_as(_expr: Expr):
        if isinstance(_expr, Neg):
            return "Neg"
        if isinstance(_expr, Sqrt):
            return "Sqrt"
        if isinstance(_expr, Sin):
            return "Sin"
        if isinstance(_expr, Cos):
            return "Cos"
        if isinstance(_expr, Arcsin):
            return "Arcsin"
        if isinstance(_expr, Arccos):
            return "Arccos"
        if isinstance(_expr, Arctan):
            return "Arctan"
        if isinstance(_expr, Add):
            return "Add"
        if isinstance(_expr, Sub):
            return "Sub"
        if isinstance(_expr, Mul):
            return "Mul"
        if isinstance(_expr, Div):
            return "Div"
        if isinstance(_expr, Pow):
            return "Pow"
        if isinstance(_expr, Variable):
            return "Variable"
        if isinstance(_expr, Constant):
            return "Constant"

    def _get_child_list(_expr: Expr):
        _child_list = list()
        _queue = [_expr]

        while len(_queue) > 0:
            _elem = _queue.pop(0)
            if isinstance(_elem, Variable):
                _child_list.append(("Variable", _elem.id))
            elif isinstance(_elem, Constant):
                _child_list.append(("Constant", _elem.value))
            elif isinstance(_elem, NonLeaf):
                _new_queue = list()
                _new_child_list = list()
                for e in _elem.children:
                    _new_child_list.append((_get_type_as(e), ""))
                    _new_queue.append(e)
                _child_list.append(_new_queue)
        return _child_list

    left_depth_list = _get_child_list(left)
    right_depth_list = _get_child_list(right)

    return left_depth_list == right_depth_list


def dynamic_syntatic_eqaulity(left: Dynamics, right: Dynamics):
    # if both are the same
    if left is None and right is None:
        return True

    # if one of them is None this is not the equal case
    if left is None or right is None:
        return False

    set_a = set(left.vars)
    set_b = set(right.vars)

    if set_a != set_b:
        return False

    if len(left.exps) != len(right.exps):
        return False

    for i, e in enumerate(left.exps):
        if left.vars[i].id == right.vars[i].id:
            if not expr_syntatic_equality_linear(e, right.exps[i]):
                return False
        else:
            return False
    # queue = set()
    # while queue != set_a:
    #     for i, e in enumerate(left.exps):
    #         for j, e1 in enumerate(right.exps):
    #             if left.vars[i].id == right.vars[j].id:
    #                 if expr_syntatic_equality_linear(e, e1):
    #                     queue.add(left.vars[i])
    #                     break
    #     break
    #
    # return queue == set_a
    return True
