SECTION_NAMES = ("common", "z3", "yices", "dreal")

SECTION_VALUE_OPTIONS = {
    "common": (
        "threshold", "bound", "time-bound", "solver", "goal",
        "time-horizon", "parallel-core", "scenario-batch-size",
        "core-minimize-attempts", "smt2-dir",
    ),
    "z3": ("logic",),
    "yices": ("logic",),
    "dreal": ("precision", "ode-order", "ode-step", "executable-path"),
}

SECTION_BOOLEAN_OPTIONS = {
    "common": (
        "two-step", "concrete", "parallel", "visualize", "verbose",
        "reach", "only-loop", "save-smt2",
    ),
    "z3": (),
    "yices": (),
    "dreal": (),
}

SECTION_TYPE_RULES = {
    "common": {
        ("threshold", "float"),
        ("bound", "integer"),
        ("time-bound", "float"),
        ("solver", frozenset({"z3", "yices", "dreal"})),
        ("goal", "string"),
        ("time-horizon", "float"),
        ("parallel-core", "integer"),
        ("scenario-batch-size", "integer"),
        ("core-minimize-attempts", "integer"),
        ("smt2-dir", "string"),
    },
    "z3": {("logic", frozenset({"QF_NRA", "QF_LRA"}))},
    "yices": {("logic", frozenset({"QF_NRA", "QF_LRA"}))},
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
    "dreal": {"ode-order", "executable-path"},
}

OPTION_HELP = {
    "file": "STLmc model file to check",
    "default-cfg": "path to the system-wide base configuration",
    "model-cfg": "path to the model configuration file",
    "model-specific-cfg": "path to the goal-specific configuration file",
    "goal": "goal name to check, or 'all'",
    "solver": "underlying solver: auto, dreal, z3, or yices",
    "bound": "maximum discrete jump bound",
    "time-bound": "maximum global trace time",
    "time-horizon": "maximum duration allowed in one mode, or 'time-bound'",
    "threshold": "robustness threshold used to relax the negated goal",
    "parallel-core": "maximum number of parallel solver workers",
    "scenario-batch-size": "number of two-step scenarios combined in one OR query",
    "core-minimize-attempts": "number of minimized unsat cores tried per scenario",
    "smt2-dir": "directory used for generated SMT2 files",
    "logic": "SMT logic used by Z3 or Yices, such as QF_LRA or QF_NRA",
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
    "only-loop": "restrict checking to loop scenarios",
    "save-smt2": "save generated SMT2 queries",
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
