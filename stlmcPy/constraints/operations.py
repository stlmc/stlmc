from functools import singledispatch
from stlmcPy.constraints.constraints import *
from stlmcPy.exception.exception import NotSupportedError


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
    return Function([substitution(const.var, substitution_dict)], [substitution(const.exp, substitution_dict)])


@substitution.register(Ode)
def _(const: Ode, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return Ode([substitution(const.var, substitution_dict)], [substitution(const.exp, substitution_dict)])


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


@singledispatch
def substitutionSize(const: Constraint, substitution_dict):
    return const, 1


@substitutionSize.register(Variable)
def _(const: Variable, substitution_dict):
    if const in substitution_dict:
        result = substitution_dict[const]
        return result, 1
    return const, 1


@substitutionSize.register(Add)
def _(const: Add, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1

    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Add(left, right), sl + rl + 1


@substitutionSize.register(Sub)
def _(const: Sub, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Sub(left, right), sl + rl + 1


@substitutionSize.register(Mul)
def _(const: Mul, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Mul(left, right), sl + rl + 1


@substitutionSize.register(Div)
def _(const: Div, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Div(left, right), sl + rl + 1


@substitutionSize.register(Pow)
def _(const: Pow, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    return Pow(left, right), sl + rl + 1


@substitutionSize.register(Neg)
def _(const: Neg, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    s, sl = substitutionSize(const.child, substitution_dict)
    return Neg(s), sl + 1


@substitutionSize.register(Function)
def _(const: Function, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1

    left, sl = substitutionSize(const.var, substitution_dict)
    right, rl = substitutionSize(const.exp, substitution_dict)
    return Function([left], [right]), sl + rl + 1


@substitutionSize.register(Ode)
def _(const: Ode, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.var, substitution_dict)
    right, rl = substitutionSize(const.exp, substitution_dict)
    return Ode([left], [right]), sl + rl + 1


@substitutionSize.register(And)
def _(const: And, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    children = list()
    total = 0
    for child in const.children:
        chi, s = substitutionSize(child, substitution_dict)
        total += s
        children.append(chi)
    return And(children), total + 1


@substitutionSize.register(Or)
def _(const: Or, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    children = list()
    total = 0
    for child in const.children:
        chi, s = substitutionSize(child, substitution_dict)
        total += s
        children.append(chi)
    return Or(children), total + 1


@substitutionSize.register(Not)
def _(const: Not, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1

    s, ss = substitutionSize(const.child, substitution_dict)
    return Not(s), ss + 1


@substitutionSize.register(Gt)
def _(const: Gt, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Gt(left, right), sl + rl + 1


@substitutionSize.register(Geq)
def _(const: Geq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Geq(left, right), sl + rl + 1


@substitutionSize.register(Lt)
def _(const: Lt, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Lt(left, right), sl + rl + 1


@substitutionSize.register(Leq)
def _(const: Leq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Leq(left, right), sl + rl + 1


@substitutionSize.register(Eq)
def _(const: Eq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Eq(left, right), sl + rl + 1


@substitutionSize.register(Neq)
def _(const: Neq, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Neq(left, right), sl + rl + 1


@substitutionSize.register(Implies)
def _(const: Implies, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    left, sl = substitutionSize(const.left, substitution_dict)
    right, rl = substitutionSize(const.right, substitution_dict)
    return Implies(left, right), sl + rl + 1


@substitutionSize.register(Forall)
def _(const: Forall, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    s, ss = substitutionSize(const.const, substitution_dict)
    return Forall(const.current_mode_number, const.end_tau, const.start_tau,
                  s, const.integral), ss + 1


@substitutionSize.register(FinallyFormula)
def _(const: FinallyFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    s, ss = substitutionSize(const.child, substitution_dict)
    return FinallyFormula(const.local_time, const.global_time, s), ss + 1


@substitutionSize.register(GloballyFormula)
def _(const: GloballyFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    s, ss = substitutionSize(const.child, substitution_dict)
    return GloballyFormula(const.local_time, const.global_time, s), ss + 1


@substitutionSize.register(UntilFormula)
def _(const: UntilFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    sl, ssl = substitutionSize(const.left, substitution_dict)
    sr, ssr = substitutionSize(const.right, substitution_dict)
    return UntilFormula(const.local_time, const.global_time,
                        sl,
                        sr), ssl + ssr + 1


@substitutionSize.register(ReleaseFormula)
def _(const: ReleaseFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const], 1
    sl, ssl = substitutionSize(const.left, substitution_dict)
    sr, ssr = substitutionSize(const.right, substitution_dict)
    return ReleaseFormula(const.local_time, const.global_time,
                          sl,
                          sr), ssl + ssr + 1


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
    return Gt(const.left, Sub(const.right, delta))


@relaxing.register(Leq)
def _(const: Leq, delta):
    return Leq(const.left, Add(const.right, delta))


@relaxing.register(Lt)
def _(const: Lt, delta):
    return Lt(const.left, Add(const.right, delta))


@relaxing.register(Eq)
def _(const: Eq, delta):
    return And([Gt(const.left, Sub(const.right, Div(delta, RealVal('2')))),
                Lt(const.left, Add(const.right, Div(delta, RealVal('2'))))])


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
            new_dict[dyn_var] = Mul(integral.dynamics.exps[index], Real('tau'))
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
        print("what happened")
        if eval(str(infix(y))) == 0:
            return RealVal("0")
        elif str(x.id)[0:3] == 'tau':
            return Mul(y, Pow(x, (Sub(y, RealVal("1")))))
        else:
            return RealVal("0")
    else:
        raise NotSupportedError('Cannot handling polynomial yet {} : {}'.format(y, const))


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
    if const.id[:-2] == "_0":
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
        return And([child.left, reduce_not(Not(child.right))])
    return const
    # raise NotSupportedError("cannot reduce given constraint: " + str(const))


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


def make_boolean_abstract_consts(props: dict()):
    result = list()
    for p in props:
        result.append(Eq(p, props[p]))
    return And(result)


@singledispatch
def infix(const: Constraint):
    return str(const)


# assumption: no mode variable exists
@infix.register(Real)
def _(const: Real):
    if "tau" in const.id:
        return const.id
    index = const.id.find("_")
    if index == -1:
        return const.id
    return const.id[:index]


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
