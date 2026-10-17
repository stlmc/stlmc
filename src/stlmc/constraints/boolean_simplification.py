"""Propagate unconditional Boolean literals without changing arithmetic.

Only positive conjunctions provide assignments. In particular, an assignment
inside an OR branch, implication, negation, or quantifier is not global.
Retaining the assignments makes the result equivalent, not merely equisatisfiable.
"""

from .constraints import And, Bool, BoolVal, Eq, Formula, Implies, Neq, Not, Or


def _truth(formula):
    if isinstance(formula, BoolVal):
        value = str(formula.value).lower()
        if value in ("true", "false"):
            return value == "true"
    return None


def propagate_boolean_constants(formula):
    assignments = {}
    pending = [formula]
    while pending:
        node = pending.pop()
        variable, value = None, None
        if isinstance(node, And):
            pending.extend(reversed(node.children))
        elif isinstance(node, Bool):
            variable, value = node, True
        elif isinstance(node, Not) and isinstance(node.child, Bool):
            variable, value = node.child, False
        elif isinstance(node, Eq):
            if isinstance(node.left, Bool):
                variable, value = node.left, _truth(node.right)
            elif isinstance(node.right, Bool):
                variable, value = node.right, _truth(node.left)
        if variable is not None and value is not None:
            if variable in assignments and assignments[variable] != value:
                return BoolVal("False")
            assignments[variable] = value

    cache = {}

    def simplify(node):
        # Identity is only a local DAG cache key, never a generated symbol.
        identity = id(node)
        if identity in cache:
            return cache[identity][1]
        result = node
        if isinstance(node, Bool) and node in assignments:
            result = BoolVal(str(assignments[node]))
        elif isinstance(node, (And, Or)):
            conjunction = isinstance(node, And)
            children = []
            for child in node.children:
                child = simplify(child)
                value = _truth(child)
                if value is not None:
                    if value != conjunction:
                        result = BoolVal(str(value))
                        break
                    continue
                children.append(child)
            else:
                if not children:
                    result = BoolVal(str(conjunction))
                elif len(children) == 1:
                    result = children[0]
                else:
                    result = type(node)(children)
        elif isinstance(node, Not):
            child = simplify(node.child)
            value = _truth(child)
            result = BoolVal(str(not value)) if value is not None else Not(child)
        elif isinstance(node, Implies):
            left, right = simplify(node.left), simplify(node.right)
            lv, rv = _truth(left), _truth(right)
            if lv is False or rv is True:
                result = BoolVal("True")
            elif lv is True:
                result = right
            elif rv is False:
                result = simplify(Not(left))
            else:
                result = Implies(left, right)
        elif isinstance(node, (Eq, Neq)) and (
                isinstance(node.left, Formula) and isinstance(node.right, Formula)):
            left, right = simplify(node.left), simplify(node.right)
            lv, rv = _truth(left), _truth(right)
            if lv is not None:
                positive = lv if isinstance(node, Eq) else not lv
                result = right if positive else simplify(Not(right))
            elif rv is not None:
                positive = rv if isinstance(node, Eq) else not rv
                result = left if positive else simplify(Not(left))
            else:
                result = type(node)(left, right)
        # Numeric atoms, integrals, and universal flow constraints are opaque.
        # Retain the input too: temporary Not nodes must not have their ids
        # recycled while this traversal is still using the cache.
        cache[identity] = (node, result)
        return result

    reduced = simplify(formula)
    if _truth(reduced) is False:
        return reduced
    if not assignments:
        return reduced
    return And([reduced, *[
        Eq(variable, BoolVal(str(value)))
        for variable, value in assignments.items()
    ]])
