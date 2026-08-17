import argparse
import re
from pathlib import Path

from ..config_schema import OPTION_HELP


DEFAULT_CONFIG_PATH = Path(__file__).resolve().parent.parent / "default.cfg"


def load_builtin_defaults(path=DEFAULT_CONFIG_PATH):
    defaults = {}
    assignment = re.compile(r"^([A-Za-z][A-Za-z0-9-]*)\s*=\s*(.*?)\s*$")
    for raw_line in Path(path).read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].strip()
        match = assignment.match(line)
        if match is None:
            continue
        name, value = match.groups()
        value = value.strip().strip('"')
        previous = defaults.get(name)
        if previous is not None and previous != value:
            raise ValueError("conflicting built-in defaults for '{}'".format(name))
        defaults[name] = value
    return defaults


BUILTIN_DEFAULTS = load_builtin_defaults()


def argument_help(name):
    description = OPTION_HELP.get(
        name, "configuration override for '{}'".format(name)
    )
    if name in BUILTIN_DEFAULTS:
        return "{} (default: {})".format(description, BUILTIN_DEFAULTS[name])
    return description


def build_parser(prog=None):
    parser = argparse.ArgumentParser(
        prog=prog,
        description="STLmc - Signal Temporal Logic Model Checker",
        formatter_class=argparse.RawTextHelpFormatter,
    )
    parser.add_argument("file", nargs="?", help=argument_help("file"))
    parser.add_argument("-default-cfg", metavar="PATH", help=argument_help("default-cfg"))
    parser.add_argument("-model-cfg", metavar="PATH", help=argument_help("model-cfg"))
    parser.add_argument("-model-specific-cfg", metavar="PATH",
                        help=argument_help("model-specific-cfg"))

    common = parser.add_argument_group("model checking")
    for name in (
        "goal", "solver", "bound", "time-bound", "time-horizon", "threshold",
        "parallel-core", "scenario-batch-size", "core-minimize-attempts", "smt2-dir",
    ):
        common.add_argument("-{}".format(name), help=argument_help(name))

    solver = parser.add_argument_group("solver options")
    for name in ("logic", "precision", "ode-order", "ode-step", "executable-path"):
        solver.add_argument("-{}".format(name), help=argument_help(name))

    flags = parser.add_argument_group("feature flags")
    for name in (
        "two-step", "concrete", "parallel", "visualize", "verbose", "reach",
        "only-loop", "save-smt2",
    ):
        flags.add_argument("-{}".format(name), action="store_true", help=argument_help(name))
    return parser


def print_help(prog=None):
    build_parser(prog=prog).print_help()
    return 0
