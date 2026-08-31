"""Traversal and structural analysis of constraint trees."""

from functools import singledispatch

from .constraints import *
from ..exceptions import NotSupportedError

def size_of_tree(tree: Tree):
    if tree is None:
        return 0
    size = 0
    waiting = [tree]
    while waiting:
        node = waiting.pop()
        if isinstance(node, Leaf):
            size += 1
        elif isinstance(node, NonLeaf):
            size += 1
            waiting.extend(node.children)
        else:
            raise NotSupportedError("cannot calculate size of {}".format(node))
    return size


def elements_of_tree(tree: Tree) -> set:
    elements = set()
    waiting = [] if tree is None else [tree]
    while waiting:
        node = waiting.pop()
        if isinstance(node, Leaf):
            elements.add(node)
        elif isinstance(node, NonLeaf):
            waiting.extend(node.children)
    return elements


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


__all__ = [
    "elements_of_tree", "fresh_new_var", "get_max_bound", "get_max_depth",
    "get_vars", "is_proposition", "size_of_tree", "subformula",
]

