import random

from stlmcPy.constraints.constraints import Interval, RealVal, GloballyFormula, FinallyFormula, universeInterval, Not, \
    UntilFormula, ReleaseFormula, Implies, And, Or, BoolVal, Bool, Constraint, BinaryTemporalFormula, \
    UnaryTemporalFormula, UnaryFormula, BinaryFormula
from stlmcPy.constraints.operations import generate_id
from stlmcPy.exception.exception import NotSupportedError


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


def set_formula(op, arity, children):
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


def rand_formula(temporal_depth: int, non_temporal_depth: int, atoms):
    # print("temporal_depth {}, non {}".format(temporal_depth, non_temporal_depth))
    if non_temporal_depth <= 0:
        return random.sample(atoms, 1)[0]

    if temporal_depth <= 0:
        formula, arity, is_atom = pick_only_non_temporal(atoms)
        if not is_atom:
            children = random.sample(atoms, arity)
            return set_formula(formula, arity, children)
        else:
            return formula

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


def generate_random_formula(file_name: str, temporal_depth: int, non_temporal_depth, total: int, variable_size: int):
    counter = 0
    atoms = generate_atoms(variable_size)
    f = open(file_name, "w")
    for i in range(total):
        counter += 1
        print("generate ({}/{})".format(counter, total))
        rf = rand_formula(temporal_depth, non_temporal_depth, atoms)
        f.write("formula ({}): {}\n".format(counter, rf))
    f.close()


# generate_random_formula("formula", 3, 5, 100, 5)
