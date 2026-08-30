import os


SECTION_NAMES = ("common", "z3", "yices", "cvc5", "dreal")

SECTION_VALUE_OPTIONS = {
    "common": (
        "threshold", "bound", "time-bound", "solver", "goal", "path-strategy",
        "time-horizon", "parallel-core", "solver-batch-size",
        "smt2-dir",
    ),
    "z3": ("logic",),
    "yices": ("logic",),
    "cvc5": ("logic",),
    "dreal": ("precision", "ode-order", "ode-step", "executable-path"),
}

SECTION_BOOLEAN_OPTIONS = {
    "common": (
        "two-step", "concrete", "parallel", "visualize", "verbose",
        "reach", "save-smt2",
    ),
    "z3": (),
    "yices": (),
    "cvc5": (),
    "dreal": (),
}

SECTION_TYPE_RULES = {
    "common": {
        ("threshold", "float"),
        ("bound", "integer"),
        ("time-bound", "float"),
        ("solver", frozenset({"auto", "z3", "yices", "cvc5", "dreal"})),
        ("goal", "string"),
        ("path-strategy", frozenset({"symbolic", "explicit"})),
        ("time-horizon", "float"),
        ("parallel-core", "integer"),
        ("solver-batch-size", "integer"),
        ("smt2-dir", "string"),
    },
    "z3": {("logic", frozenset({"QF_NRA", "QF_LRA"}))},
    "yices": {("logic", frozenset({"QF_NRA", "QF_LRA"}))},
    "cvc5": {("logic", frozenset({"QF_NRA", "QF_LRA"}))},
    "dreal": {
        ("precision", "float"),
        ("ode-order", "float"),
        ("ode-step", "float"),
        ("executable-path", "path"),
    },
}

SECTION_MANDATORY_OPTIONS = {
    "common": {"bound", "time-bound"},
    "z3": set(),
    "yices": set(),
    "cvc5": set(),
    "dreal": {"ode-order", "executable-path"},
}

OPTION_HELP = {
    "file": "STLmc model file to check",
    "default-cfg": "path to the system-wide base configuration",
    "model-cfg": "path to the model configuration file",
    "model-specific-cfg": "path to the goal-specific configuration file",
    "goal": "goal name to check, or 'all'",
    "path-strategy": (
        "discrete path handling\n"
        "choices: symbolic, explicit"
    ),
    "solver": (
        "underlying solver\n"
        "choices: auto, cvc5, dreal, z3, yices"
    ),
    "bound": "maximum mode changes and variable points (reach: jumps)",
    "time-bound": "maximum global trace time",
    "time-horizon": "maximum duration of each continuous segment, or 'time-bound'",
    "threshold": "robustness threshold used to relax the negated goal",
    "parallel-core": "maximum number of parallel solver workers",
    "solver-batch-size": "maximum candidates combined in one solver OR query",
    "smt2-dir": "directory used for generated SMT2 files",
    "logic": (
        "SMT logic used by CVC5, Z3, or Yices\n"
        "choices: QF_LRA, QF_NRA"
    ),
    "precision": "dReal delta precision",
    "ode-order": "dReal ODE integration order",
    "ode-step": "dReal ODE integration step; omit for automatic control",
    "executable-path": "path to the underlying solver executable",
    "two-step": "enable two-step scenario enumeration",
    "concrete": "disable unsat-core scenario generalization",
    "parallel": "run refinement checks in parallel",
    "visualize": "write a counterexample or witness artifact",
    "verbose": "print detailed progress information",
    "reach": "treat an ordinary state goal as a reachability query",
    "save-smt2": "save generated SMT2 queries",
}

OPTION_CHOICES = {
    "solver": ("auto", "cvc5", "dreal", "z3", "yices"),
    "path-strategy": ("symbolic", "explicit"),
    "logic": ("QF_LRA", "QF_NRA"),
}


def all_value_options():
    return {
        option
        for section in SECTION_NAMES
        for option in SECTION_VALUE_OPTIONS[section]
    }


def all_boolean_options():
    return {
        option
        for section in SECTION_NAMES
        for option in SECTION_BOOLEAN_OPTIONS[section]
    }


def resolve_parallel_core(value, cpu_count=None):
    if str(value).lower() != "auto":
        return str(value)
    available = os.cpu_count() if cpu_count is None else cpu_count
    return str(max(1, available or 1))
