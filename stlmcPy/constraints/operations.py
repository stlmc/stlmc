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
    return Add(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Sub)
def _(const: Sub, substitution_dict):
    return Sub(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Mul)
def _(const: Mul, substitution_dict):
    return Mul(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Div)
def _(const: Div, substitution_dict):
    return Div(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Pow)
def _(const: Pow, substitution_dict):
    return Pow(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Neg)
def _(const: Neg, substitution_dict):
    return Neg(substitution(const.child, substitution_dict))


@substitution.register(Function)
def _(const: Function, substitution_dict):
    return Function(substitution(const.var, substitution_dict), substitution(const.exp, substitution_dict))


@substitution.register(Ode)
def _(const: Ode, substitution_dict):
    return Ode(substitution(const.var, substitution_dict), substitution(const.exp, substitution_dict))


@substitution.register(And)
def _(const: And, substitution_dict):
    children = list()
    for child in const.children:
        children.append(substitution(child, substitution_dict))
    return And(children)


@substitution.register(Or)
def _(const: Or, substitution_dict):
    children = list()
    for child in const.children:
        children.append(substitution(child, substitution_dict))
    return Or(children)


@substitution.register(Not)
def _(const: Not, substitution_dict):
    return Not(substitution(const.child, substitution_dict))


@substitution.register(Gt)
def _(const: Gt, substitution_dict):
    return Gt(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Geq)
def _(const: Geq, substitution_dict):
    return Geq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Lt)
def _(const: Lt, substitution_dict):
    return Lt(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Leq)
def _(const: Leq, substitution_dict):
    return Leq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Eq)
def _(const: Eq, substitution_dict):
    return Eq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Neq)
def _(const: Neq, substitution_dict):
    return Neq(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Implies)
def _(const: Implies, substitution_dict):
    return Implies(substitution(const.left, substitution_dict), substitution(const.right, substitution_dict))


@substitution.register(Forall)
def _(const: Forall, substitution_dict):
    return Forall(const.current_mode_number, const.end_tau, const.start_tau,
                  substitution(const.const, substitution_dict), const.integral)


@substitution.register(FinallyFormula)
def _(const: FinallyFormula, substitution_dict):
    return FinallyFormula(const.local_time, const.global_time, substitution(const.child, substitution_dict))


@substitution.register(GloballyFormula)
def _(const: GloballyFormula, substitution_dict):
    return GloballyFormula(const.local_time, const.global_time, substitution(const.child, substitution_dict))


@substitution.register(UntilFormula)
def _(const: UntilFormula, substitution_dict):
    return UntilFormula(const.local_time, const.global_time,
                        substitution(const.left, substitution_dict),
                        substitution(const.right, substitution_dict))


@substitution.register(ReleaseFormula)
def _(const: ReleaseFormula, substitution_dict):
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


@reverse_inequality.register(Geq)
def _(const):
    return const


@reverse_inequality.register(Lt)
def _(const):
    return Gt(Neg(const.left), Neg(const.right))


@reverse_inequality.register(Leq)
def _(const):
    return Geq(Neg(const.left), Neg(const.right))


@singledispatch
def diff(const: Constraint):
    raise NotImplementedError('Something wrong')


@diff.register(Constant)
def _(const):
    return RealVal("0")


@diff.register(Variable)
def _(const):
    if str(const.id)[0:3] == 'tau':
        return RealVal("1")
    else:
        return RealVal("0")


@diff.register(Add)
def _(const):
    x = const.left
    y = const.right

    if len(get_vars(const)) == 0:
        return RealVal("0")
    if len(get_vars(x)) == 0:
        return diff(y)
    if len(get_vars(y)) == 0:
        return diff(x)

    return Add(diff(x), diff(y))


@diff.register(Sub)
def _(const):
    x = const.left
    y = const.right

    if len(get_vars(const)) == 0:
        return RealVal("0")
    if len(get_vars(x)) == 0:
        return diff(y)
    if len(get_vars(y)) == 0:
        return diff(x)

    return Sub(diff(x), diff(y))


@diff.register(Pow)
def _(const):
    x = const.left
    y = const.right

    if isinstance(x, Variable) and (len(get_vars(y)) == 0):
        if eval(str(y)) == 0:
            return RealVal("0")
        elif str(x.id[0:3] == 'tau'):
            return Mul(y, Pow(x, (Sub(y, RealVal("1")))))
        else:
            return RealVal("0")
    else:
        print(type(const))
        print(const)
        raise NotSupportedError('Cannot hanlindg polynomial yet')


@diff.register(Mul)
def _(const):
    x = const.left
    y = const.right

    if len(get_vars(const)) == 0:
        return RealVal("0")
    if len(get_vars(x)) == 0:
        return Mul(x, diff(y))
    if len(get_vars(y)) == 0:
        return Mul(diff(x), y)

    return Add(Mul(diff(x), y), Mul(x, diff(y)))


@diff.register(Div)
def _(const):
    x = const.left
    y = const.right
    if len(get_vars(const)) == 0:
        return RealVal("0")
    if len(get_vars(x)) == 0:
        return Sub(RealVal("0"), Div(Mul(diff(y), x), Mul(y, y)))
    if len(get_vars(y)) == 0:
        return Div(diff(x), y)

    return Sub(Div(diff(x), y), Div(Mul(diff(y), x), Mul(y, y)))


@diff.register(Neg)
def _(const):
    x = diff(const.child)
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
    if const.id[-2:] == "_0":
        return op_dict[const.__class__](const.id[-2:] + "_t")
    return const


def generate_id(initial, gid='v'):
    counter = initial
    while True:
        yield gid + str(counter)
        counter += 1
