from functools import singledispatch
from typing import Dict, Union, Set

from .generator import *
from ..constraints import *
from itertools import combinations

from ...exception.exception import NotSupportedError


class Substitution:
    def __init__(self):
        self._subst_dict: Dict[Formula, Formula] = dict()

    def add(self, src: Formula, dst: Formula):
        self._subst_dict[src] = dst

    def substitute(self, formula: Formula):
        return _substitution(formula, self._subst_dict)


class VarSubstitution:
    def __init__(self):
        self._subst_dict: Dict[Variable, Expr] = dict()

    def add(self, src: Variable, dst: Expr):
        self._subst_dict[src] = dst

    def substitute(self, formula: Formula):
        return _substitution(formula, self._subst_dict)


def inf(interval: Interval) -> Union[Real, RealVal]:
    return interval.left


def sup(interval: Interval) -> Union[Real, RealVal]:
    return interval.right


@singledispatch
def _substitution(const: Union[Formula, Expr], substitution_dict):
    return const


@_substitution.register(Variable)
def _(const: Variable, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    return const


@_substitution.register(UnaryExpr)
def _(const: UnaryExpr, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    else:
        child = _substitution(const.child, substitution_dict)
        return unary_expr(child, const.type)


@_substitution.register(BinaryExpr)
def _(const: BinaryExpr, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    else:
        left = _substitution(const.left, substitution_dict)
        right = _substitution(const.right, substitution_dict)
        return binary_expr(left, right, const.type)


@_substitution.register(UnaryFormula)
def _(const: UnaryFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    else:
        child = _substitution(const.child, substitution_dict)
        return unary_formula(child, const.type)


@_substitution.register(BinaryFormula)
def _(const: BinaryFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    else:
        left = _substitution(const.left, substitution_dict)
        right = _substitution(const.right, substitution_dict)
        return binary_formula(left, right, const.type)


@_substitution.register(MultinaryFormula)
def _(const: MultinaryFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    else:
        children = [_substitution(c, substitution_dict) for c in const.children]
        return multinary_formula(children, const.type)


@_substitution.register(Proposition)
def _(const: Proposition, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    else:
        if isinstance(const, Binary):
            left = _substitution(const.left, substitution_dict)
            right = _substitution(const.right, substitution_dict)
            return binary_proposition(left, right, const.type)
        else:
            assert isinstance(const, Integral) or isinstance(const, Forall)

            if isinstance(const, Forall):
                e_t = _substitution(const.end_tau, substitution_dict)
                s_t = _substitution(const.start_tau, substitution_dict)
                c = _substitution(const.const, substitution_dict)
                return Forall(const.current_mode_number, e_t, s_t, c)

            if isinstance(const, Integral):
                e_v = [_substitution(v, substitution_dict) for v in const.end_vector]
                s_v = [_substitution(v, substitution_dict) for v in const.start_vector]
                dyn = _dynamics_substitution(const.dynamics, substitution_dict)
                return Integral(const.current_mode_number, e_v, s_v, dyn)


@_substitution.register(UnaryTemporalFormula)
def _(const: UnaryTemporalFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    else:
        child = _substitution(const.child, substitution_dict)
        return unary_temporal_formula(const.local_time, const.global_time, child, const.type)


@_substitution.register(BinaryTemporalFormula)
def _(const: BinaryTemporalFormula, substitution_dict):
    if const in substitution_dict:
        return substitution_dict[const]
    else:
        left = _substitution(const.left, substitution_dict)
        right = _substitution(const.right, substitution_dict)
    return binary_temporal_formula(const.local_time, const.global_time, left, right, const.type)


def _dynamics_substitution(dyn: Dynamics, substitution_dict):
    vs = [_substitution(var, substitution_dict) for var in dyn.vars]
    es = [_substitution(exp, substitution_dict) for exp in dyn.exps]
    return dynamics(vs, es, dyn.type)


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
def get_vars(const: Union[Formula, Expr]):
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
    return set()


@get_vars.register(Forall)
def _(const: Forall):
    return get_vars(const.const)


@singledispatch
def reverse_inequality(const: Formula):
    return const


@reverse_inequality.register(Lt)
def _(const):
    return Gt(Neg(const.left), Neg(const.right))


@reverse_inequality.register(Leq)
def _(const):
    return Geq(Neg(const.left), Neg(const.right))


def diff(exp: Expr, integral: Integral):
    alpha = make_diff_mapping(integral)
    new_exp = _substitution(exp, alpha)

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
def diff_aux(const: Formula):
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
def substitution_zero2t(const: Formula):
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
def reduce_not(const: Formula):
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


@reduce_not.register(EqFormula)
def _(const: EqFormula):
    return EqFormula(reduce_not(const.left), reduce_not(const.right))


@reduce_not.register(NeqFormula)
def _(const: NeqFormula):
    return NeqFormula(reduce_not(const.left), reduce_not(const.right))


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
def bound_tau_max(const: Formula, tb):
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
def infix(const: Formula):
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
def clause(const: Formula):
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


def get_max_depth(const: Formula):
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


def sub_formula(formula: Formula) -> Set[Formula]:
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

        if isinstance(f, Proposition):
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


def variable_equal(v1: Variable, v2: Variable):
    return v1.type == v2.type and v1.id == v2.id
