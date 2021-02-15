from functools import singledispatch, reduce
from itertools import product

from sympy import symbols, StrictGreaterThan, GreaterThan, StrictLessThan, LessThan, Equality, Unequality, simplify, \
    core

from stlmcPy.constraints.constraints import *
from stlmcPy.constraints.operations import get_vars, clause
from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.solver.z3 import Z3Solver


def unit_split(given_set: set, i: int):
    forall_set = set()
    integral_set = set()
    tau_set = set()
    guard_set = set()
    reset_set = set()
    init_set = set()

    s_diff = set()

    for c in given_set:
        if isinstance(c, Not):
            s_diff.add(c)

    given_set = given_set.difference(s_diff)

    for c in given_set:
        var_set = get_vars(c)
        if len(var_set) == 1:
            for var in var_set:
                start_index = int(var.id.find("_"))
                if var.id[
                   start_index:] == "_0_0" and "newTau" not in var.id and "newIntegral" not in var.id and "invAtomicID" not in var.id:
                    init_set.add(c)
                    s_diff.add(c)
                    break

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        var_set = get_vars(c)
        for var in var_set:
            start_index = int(var.id.find("_"))
            s_index = int(var.id.find("_"))
            e_index = int(var.id.rfind("_"))
            bound_index = int(var.id.rfind("_"))
            if not (s_index == -1) and ((s_index == e_index and "tau" not in var.id)
                                        or ("invAtomicID" in var.id) or ("newPropDecl" in var.id)):
                bound = int(var.id[bound_index + 1:])
                if i == bound:
                    forall_set.add(c)
                    s_diff.add(c)
                    break
            elif var.id[:start_index] == "newIntegral":
                bound = int(var.id[bound_index + 1:])
                if i == bound:
                    integral_set.add(c)
                    s_diff.add(c)
                    break

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        var_set = get_vars(c)
        max_bound = -1
        for var in var_set:
            start_index = int(var.id.find("_"))
            if var.id[:start_index] == "tau":
                bound = int(var.id[start_index + 1:])
                if max_bound < bound:
                    max_bound = bound
        if (max_bound == 0 and i == 0) or (max_bound != -1 and max_bound == i + 1):
            tau_set.add(c)
            s_diff.add(c)
        elif isinstance(c, Bool):
            if "newTau" in c.id and int(c.id[-1]) == i:
                tau_set.add(c)
                s_diff.add(c)

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        if isinstance(c, Eq):
            if isinstance(c.left, Variable):
                start_index = int(c.left.id.find("_"))
                end_index = int(c.left.id.rfind("_"))
                if start_index < end_index:
                    bound = int(c.left.id[start_index + 1:end_index])
                    if c.left.id[end_index + 1:] == "0" and bound == i + 1:
                        reset_set.add(c)
                        s_diff.add(c)

    given_set = given_set.difference(s_diff)
    s_diff = set()

    for c in given_set:
        var_set = get_vars(c)
        flag = True
        for var in var_set:
            start_index = int(var.id.find("_"))
            s_index = int(var.id.find("_"))
            e_index = int(var.id.rfind("_"))
            end_index = int(var.id.rfind("_"))
            if not (s_index == e_index or "newIntegral" in var.id or "invAtomicID" in var.id
                    or "newPropDecl" in var.id or "newTau" in var.id or "reach_goal" in var.id or "chi" in var.id):
                bound = int(var.id[start_index + 1:end_index])
                last_str = var.id[-1]
                if not ((bound == i and last_str == "t") or (bound == i + 1 and last_str == "0")):
                    flag = False
                if isinstance(c.left, Real):
                    if c.left.id[e_index + 1:] == "0":
                        flag = False
                        break
            else:
                flag = False
        if flag:
            guard_set.add(c)
            s_diff.add(c)
        if isinstance(c, Bool):
            if "reach_goal_" in c.id:
                guard_set.add(c)

    return forall_set, integral_set, init_set, tau_set, reset_set, guard_set


def make_tau_guard(tau_dict, max_bound):
    result = list()
    for i in range(max_bound):
        sub = dict()
        for k in tau_dict:
            if "newTau" in k.id:
                if k.id[-1] == str(i):
                    or_literals = set()
                    for e in tau_dict[k].children:
                        or_literals.add(e)
                    sub[k] = or_literals
        result.append(sub)
    return result


def make_boolean_abstract(abstracted_consts):
    index = 0
    new_id = "new_boolean_var_"
    clause_list = clause(abstracted_consts)
    sub_dict = dict()
    original_bool = list()

    solver = Z3Solver()
    solver.set_logic("lra")

    for c in clause_list:
        if not isinstance(c, Bool):
            sub_dict[c] = Bool(new_id + str(index))
            index += 1
        else:
            original_bool.append(c)

    boolean_abstracted = solver.substitution(abstracted_consts, sub_dict)

    for o in original_bool:
        sub_dict[o] = o
    return boolean_abstracted, sub_dict


def make_reset_pool(s_i_reset):
    s_i_pool = list()
    s_v = set()
    for c in s_i_reset:
        s_v = s_v.union(get_vars(c.left))

    s_i_r = s_i_reset
    s_diff = set()

    for v in s_v:
        s_l = set()
        for c in s_i_r:
            if c.left.id == v.id:
                s_l.add(c)
                s_diff.add(c)
        s_i_r = s_i_r.difference(s_diff)
        s_i_pool.append(s_l)

    tuple_to_set = list(product(*s_i_pool))
    s_i_pool = list()
    for i in tuple_to_set:
        chi = [element for tupl in i for element in (tupl if isinstance(tupl, tuple) else (tupl,))]
        s_i_pool.append(set(chi))

    return s_i_pool


def get_bound(mapping_info: dict):
    max_bound = -1
    for key in mapping_info:
        # for forall
        if isinstance(key, Bool):
            if "newIntegral" in key.id:
                index = int(key.id.rfind("_")) + 1
                bound = int(key.id[index:])
                if max_bound < bound:
                    max_bound = bound
    return max_bound


def gen_sigma(s: set, op: str):
    sigma = dict()
    index = 0
    for c in s:
        v = Bool("new#" + str(index) + op)
        sigma[v] = c
        index += 1
    return sigma


def gen_net_assignment(mapping: dict, range_dict: dict):
    new_dict = dict()
    for var in mapping:
        search_index = var.id.find("_")
        search_id = var.id[:search_index]
        if not (Bool(var.id) in range_dict or Real(search_id) in range_dict or Real(
                var.id) in range_dict or "tau" in var.id):
            new_dict[var] = mapping[var]
    return new_dict


@singledispatch
def remove_index(c: Constraint) -> Variable:
    raise NotSupportedError("input should be variable type : " + str(c))


@remove_index.register(Variable)
def _(v: Variable) -> Variable:
    if "tau" not in v.id and "_" in v.id:
        start_index = v.id.find("_")
        var_id = v.id[:start_index]
        return Real(var_id)
    return v


def get_vars_from_set(set_of_list: list):
    result_set = set()
    for s in set_of_list:
        for c in s:
            result_set = result_set.union(get_vars(c))

    s_diff = set()
    for s in result_set:
        if isinstance(s, Integral):
            s_diff.add(s)
    result_set = result_set.difference(s_diff)
    return result_set


def find_index(input_list: list, v: Variable):
    index = 0
    for e in input_list:
        if e == remove_index(v).id:
            return index
        index += 1
    raise NotFoundElementError(v, "index not found")


@singledispatch
def expr_to_sympy(const: Constraint):
    raise NotSupportedError("cannot make it canonical : {} of type {}".format(const, type(const)))


@expr_to_sympy.register(Variable)
def _(const: Variable):
    return symbols(const.id)


@expr_to_sympy.register(Constant)
def _(const: Constant):
    return float(const.value)


@expr_to_sympy.register(Neg)
def _(const: Neg):
    return - expr_to_sympy(const.child)


@expr_to_sympy.register(Add)
def _(const: Add):
    return expr_to_sympy(const.left) + expr_to_sympy(const.right)


@expr_to_sympy.register(Sub)
def _(const: Sub):
    return expr_to_sympy(const.left) - expr_to_sympy(const.right)


@expr_to_sympy.register(Mul)
def _(const: Mul):
    return expr_to_sympy(const.left) * expr_to_sympy(const.right)


@expr_to_sympy.register(Div)
def _(const: Div):
    return expr_to_sympy(const.left) / expr_to_sympy(const.right)


@expr_to_sympy.register(Pow)
def _(const: Pow):
    return expr_to_sympy(const.left) ** expr_to_sympy(const.right)
    # if isinstance(const.left, RealVal):
    #     exponent = int(const.right.value)
    #     if exponent == 0:
    #         return core.numbers.One
    #     elif exponent == 1:
    #         return expr_to_sympy(const.left)
    #     else:
    #         print("svivivi")
    #         base = expr_to_sympy(const.left)
    #         base_list = list()
    #         for _ in range(exponent):
    #             base_list.append(base)
    #         return reduce(lambda x, y: x * y, base_list)
    # raise NotSupportedError("Pow only supports real constant exponent")


@expr_to_sympy.register(Gt)
def _(const: Gt):
    return StrictGreaterThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Geq)
def _(const: Geq):
    return GreaterThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Lt)
def _(const: Lt):
    return StrictLessThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Leq)
def _(const: Leq):
    return LessThan(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Eq)
def _(const: Eq):
    return Equality(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Neq)
def _(const: Neq):
    return Unequality(expr_to_sympy(const.left), expr_to_sympy(const.right))


@expr_to_sympy.register(Forall)
def _(const: Forall):
    return expr_to_sympy(const.const)


# optimize version translator

@singledispatch
def expr_to_sympy_inequality(const: Constraint):
    raise NotSupportedError("cannot make it canonical : {} of type {}".format(const, type(const)))


@expr_to_sympy_inequality.register(Variable)
def _(const: Variable):
    return symbols(const.id)


@expr_to_sympy_inequality.register(Constant)
def _(const: Constant):
    return float(const.value)


@expr_to_sympy_inequality.register(Neg)
def _(const: Neg):
    return - expr_to_sympy(const.child)


@expr_to_sympy_inequality.register(Add)
def _(const: Add):
    return expr_to_sympy_inequality(const.left) + expr_to_sympy_inequality(const.right)


@expr_to_sympy_inequality.register(Sub)
def _(const: Sub):
    return expr_to_sympy_inequality(const.left) - expr_to_sympy_inequality(const.right)


@expr_to_sympy_inequality.register(Mul)
def _(const: Mul):
    return expr_to_sympy_inequality(const.left) * expr_to_sympy_inequality(const.right)


@expr_to_sympy_inequality.register(Div)
def _(const: Div):
    return expr_to_sympy_inequality(const.left) / expr_to_sympy_inequality(const.right)


@expr_to_sympy_inequality.register(Pow)
def _(const: Pow):
    return expr_to_sympy_inequality(const.left) ** expr_to_sympy_inequality(const.right)


@expr_to_sympy_inequality.register(Gt)
def _(const: Gt):
    # should be StrictGreaterThan
    # but for flowstar we use greater than
    return StrictGreaterThan(simplify(expr_to_sympy_inequality(const.left) - expr_to_sympy_inequality(const.right)), 0)


@expr_to_sympy_inequality.register(Geq)
def _(const: Geq):
    return GreaterThan(simplify(expr_to_sympy_inequality(const.left) - expr_to_sympy_inequality(const.right)), 0)


@expr_to_sympy_inequality.register(Lt)
def _(const: Lt):
    # should be StrictLessThan
    # but for flowstar we use greater than
    return StrictLessThan(simplify(expr_to_sympy_inequality(const.left) - expr_to_sympy_inequality(const.right)), 0)


@expr_to_sympy_inequality.register(Leq)
def _(const: Leq):
    return LessThan(simplify(expr_to_sympy_inequality(const.left) - expr_to_sympy_inequality(const.right)), 0)


@expr_to_sympy_inequality.register(Eq)
def _(const: Eq):
    return Equality(simplify(expr_to_sympy_inequality(const.left) - expr_to_sympy_inequality(const.right)), 0)


@expr_to_sympy_inequality.register(Neq)
def _(const: Neq):
    return Unequality(simplify(expr_to_sympy_inequality(const.left) - expr_to_sympy_inequality(const.right)), 0)


@expr_to_sympy_inequality.register(Forall)
def _(const: Forall):
    return expr_to_sympy_inequality(const.const)
