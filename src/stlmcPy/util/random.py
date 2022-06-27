import random

from ..constraints.constraints import *
from ..constraints.operations import generate_id
from ..exception.exception import NotSupportedError


def pick():
    operator_pool = [(FinallyFormula, 1, True), (GloballyFormula, 1, True), (ReleaseFormula, 2, True),
                     (UntilFormula, 2, True)]
    operator_pool.extend([(And, 3, False), (Or, 3, False), (Implies, 2, False), (Not, 1, False)])
    return random.sample(operator_pool, 1)[0]


def pick_only_non_temporal(atoms):
    operator_pool = [(And, 3, False), (Or, 3, False), (Implies, 2, False), (Not, 1, False)]
    for a in atoms:
        operator_pool.append((a, 0, True))
    return random.sample(operator_pool, 1)[0]


def pick_only_temporal():
    operator_pool = [(FinallyFormula, 1, True), (GloballyFormula, 1, True), (ReleaseFormula, 2, True),
                     (UntilFormula, 2, True)]
    return random.sample(operator_pool, 1)[0]


def generate_interval():
    lend = True if random.getrandbits(1) else False
    rend = True if random.getrandbits(1) else False
    lval_raw = random.uniform(0, 30)
    rval_raw = lval_raw + random.uniform(0, 30)
    return Interval(lend, RealVal(str(lval_raw)), rend, RealVal(str(rval_raw)))


def generate_atoms(variable_size: int):
    assert variable_size >= 1
    gen = generate_id(1, "p")
    atoms = list()
    atoms.extend([Bool(str(next(gen))) for _ in range(variable_size)])
    return atoms


def add_uncertainty(pool):
    assert len(pool) > 2
    new_pool = pool.copy()
    size = int(len(pool) / 2)
    np = random.sample(pool, size)
    for p in np:
        # add one of them
        new_pool.append(Not(p))
        new_pool.append(And([p, Not(p)]))
        new_pool.append(Implies(p, Not(p)))
        new_pool.append(Implies(Not(p), p))
    return new_pool


def set_formula(op, arity, children) -> Constraint:
    if arity == 0:
        return op

    local_time = generate_interval()
    global_time = generate_interval()

    if op is FinallyFormula or op is GloballyFormula:
        return op(local_time, global_time, random.sample(children, 1)[0])

    if op is Not:
        return op(random.sample(children, 1)[0])

    if op is UntilFormula or op is ReleaseFormula:
        local_time = generate_interval()
        global_time = generate_interval()
        seed = random.sample(children, 2)
        left = seed[0]
        right = seed[1]
        return op(local_time, global_time, left, right)

    if op is Implies:
        seed = random.sample(children, 2)
        left = seed[0]
        right = seed[1]
        return op(left, right)

    if op is And or op is Or:
        max_range = min(len(children), 6)
        c = random.randrange(1, max_range, 1)
        return op(random.sample(children, c))
    else:
        raise NotSupportedError("cannot take arity {} for {}".format(arity, op))


def make_empty_formula(op, arity) -> Constraint:
    if arity == 0:
        return op

    local_time = generate_interval()
    global_time = generate_interval()

    if op is FinallyFormula or op is GloballyFormula:
        return op(local_time, global_time, None)

    if op is Not:
        return op(None)

    if op is UntilFormula or op is ReleaseFormula:
        local_time = generate_interval()
        global_time = generate_interval()
        return op(local_time, global_time, None, None)

    if op is Implies:
        return op(None, None)

    if op is And or op is Or:
        return op(list())
    else:
        raise NotSupportedError("cannot take arity {} for {}".format(arity, op))


def make_formula(op: Constraint, child: Constraint):
    if isinstance(op, Bool):
        return op

    if isinstance(op, FinallyFormula) or isinstance(op, GloballyFormula) or isinstance(op, Not):
        if op.child is None:
            op.child = child
        return op

    if isinstance(op, UntilFormula) or isinstance(op, ReleaseFormula) or isinstance(op, Implies):
        if op.left is None:
            op.left = child
        elif op.right is None:
            op.right = child
        return op

    if isinstance(op, And) or isinstance(op, Or):
        if op.children is not None:
            op.children.append(child)
        else:
            op.children = [child]
        return op
    else:
        raise NotSupportedError("cannot make formula : {}, {}, {}".format(op, type(op), child))


def set_formula_with(op, arity, child, children):
    if op is FinallyFormula or op is GloballyFormula or op is Not:
        return set_formula(op, arity, [child])

    if op is UntilFormula or op is ReleaseFormula or op is Implies:
        new_children = [child, random.sample(children, 1)[0]]
        return set_formula(op, arity, new_children)

    if op is And or op is Or:
        max_range = min(len(children), 6)
        c = random.randrange(1, max_range, 1)
        return op([child, random.sample(children, c - 1)])
    else:
        raise NotSupportedError("cannot take arity {} for {}".format(arity, op))


def generate_non_termporal_formula(atoms):
    formula, arity, is_atom = pick_only_non_temporal(atoms)
    if not is_atom:
        children = random.sample(atoms, arity)
        return set_formula(formula, arity, children)
    else:
        return formula


def gen_non_temporal(temporal_depth, non_temporal_depth, atoms):
    op, arity, _ = pick_only_non_temporal(atoms)
    children = list()
    for _ in range(random.randrange(4, 12, 1)):
        child = rand_formula(temporal_depth, non_temporal_depth - 1, atoms)
        children.append(child)
    return set_formula(op, arity, add_uncertainty(children))


def gen_temporal(temporal_depth, non_temporal_depth, atoms):
    op, arity, _ = pick_only_temporal()
    children = list()
    for _ in range(random.randrange(4, 12, 1)):
        child = rand_formula(temporal_depth - 1, non_temporal_depth, atoms)
        children.append(child)
    return set_formula(op, arity, add_uncertainty(children))


def rand_formula(temporal_depth: int, non_temporal_depth: int, atoms):
    # print("temporal_depth {}, non {}".format(temporal_depth, non_temporal_depth))
    if non_temporal_depth <= 0 and temporal_depth <= 0:
        formula, arity, is_atom = pick_only_non_temporal(atoms)
        if not is_atom:
            children = random.sample(atoms, arity)
            return set_formula(formula, arity, children)
        else:
            return formula

    if non_temporal_depth <= 0:
        return gen_temporal(temporal_depth, non_temporal_depth, atoms)

    if temporal_depth <= 0:
        return gen_non_temporal(temporal_depth, non_temporal_depth, atoms)

    op, arity, is_temporal = pick()

    if is_temporal:
        children = list()
        for _ in range(random.randrange(4, 12, 1)):
            child = rand_formula(temporal_depth - 1, non_temporal_depth, atoms)
            children.append(child)
        return set_formula(op, arity, add_uncertainty(children))
    else:
        children = list()
        for _ in range(random.randrange(4, 12, 1)):
            child = rand_formula(temporal_depth, non_temporal_depth - 1, atoms)
            children.append(child)
        return set_formula(op, arity, add_uncertainty(children))


def rand_formula2(temporal_depth: int, non_temporal_depth: int, atoms):
    # print("temporal_depth {}, non {}".format(temporal_depth, non_temporal_depth))
    if temporal_depth <= 0:
        return generate_non_termporal_formula(atoms)

    op, arity, is_temporal = pick_only_temporal()

    pool = list()
    child = rand_formula2(temporal_depth - 1, non_temporal_depth, atoms)
    for _ in range(random.randrange(4, 12, 1)):
        pool.append(generate_non_termporal_formula(atoms))
    return set_formula_with(op, arity, child, add_uncertainty(pool))


def rand_formula3(temporal_depth: int, tree_depth: int, atoms):
    assert temporal_depth < tree_depth - 1

    def _make_random_formula():
        formula, arity, is_atom = pick_only_non_temporal(atoms)
        if not is_atom:
            children = random.sample(add_uncertainty(atoms), arity)
            return set_formula(formula, arity, children)
        else:
            return formula

    depth_to_be_in = random.sample(range(1, tree_depth - 1), temporal_depth)
    # 1: Until
    # 2: Release
    # 3: Eventually
    # 4: Finally
    # 5: And
    # 6: Or
    # 7: Implies
    # 8: Not
    # 9: Atom
    # 10: any
    elements = list()
    for depth in reversed(range(1, tree_depth + 1)):
        depth_list = list()
        for width in range(2 ** (depth - 1)):
            if depth in depth_to_be_in:
                depth_list.append(random.randrange(1, 5))
            elif depth == tree_depth:
                depth_list.append(9)
            else:
                depth_list.append(random.randrange(5, 10))
        elements.append(depth_list)

    assert len(elements) == tree_depth

    op_dict = {1: UntilFormula, 2: ReleaseFormula, 3: FinallyFormula,
               4: GloballyFormula,
               5: And, 6: Or, 7: Implies, 8: Not, 9: Bool}

    arity_dict = {1: 2, 2: 2, 3: 1, 4: 1, 5: 3, 6: 3, 7: 2, 8: 1, 9: 0}
    # make initial elements_pool
    elements_pool = [_make_random_formula() for _ in range(len(elements[0]))]
    for i, depth_list in enumerate(elements):
        if i > 0:
            new_elements_pool = list()
            for e in depth_list:
                # roughly build elements
                child_num = random.randrange(max(1, len(elements_pool) - 4), len(elements_pool))
                children = list()
                for _ in range(child_num):
                    children.append(random.sample(elements_pool, 1)[0])
                if arity_dict[e] >= 3:
                    new_elements_pool.append(op_dict[e](children))
                elif arity_dict[e] == 2:
                    new_child_pool = list()
                    new_child_pool.append(random.sample(children, 1)[0])
                    new_child_pool.append(random.sample(children, 1)[0])
                    if e <= 2:
                        local_time = generate_interval()
                        global_time = generate_interval()
                        new_elements_pool.append(op_dict[e](local_time, global_time, new_child_pool[0], new_child_pool[1]))
                    else:
                        new_elements_pool.append(op_dict[e](new_child_pool[0], new_child_pool[1]))
                elif arity_dict[e] == 1:
                    if 3 <= e <= 4:
                        local_time = generate_interval()
                        global_time = generate_interval()
                        new_elements_pool.append(op_dict[e](local_time, global_time, random.sample(children, 1)[0]))
                    else:
                        new_elements_pool.append(op_dict[e](random.sample(children, 1)[0]))
                else:
                    new_elements_pool.append(random.sample(atoms, 1)[0])
            elements_pool = new_elements_pool
    return elements_pool[0]


def generate_random_formula(file_name: str, temporal_depth: int, non_temporal_depth, total: int, variable_size: int,
                            rand_func):
    counter = 0
    atoms = generate_atoms(variable_size)
    f = open(file_name, "w")
    for i in range(total):
        counter += 1
        print("generate ({}/{})".format(counter, total))
        rf = rand_func(temporal_depth, non_temporal_depth, atoms)
        f.write("formula ({}): {}\n".format(counter, rf))
    f.close()

# generate_random_formula("formula", 3, 5, 100, 5)
