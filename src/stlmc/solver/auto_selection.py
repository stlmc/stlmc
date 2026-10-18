"""Select a usable runtime backend without installing or importing it here."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
from fractions import Fraction

from ..constraints.analysis import get_vars
from ..constraints.constraints import Binary, Div, Dynamics, Mul, Multinary, Ode, Pow, Unary
from ..constraints.substitution import substitution
from ..exceptions import ElementNotFoundError, NotSupportedError, SolverUnavailableError
from .availability import find_dreal
from .capability import (
    expression_requires_dreal, model_requires_dreal,
    validate_formula_solver_support, validate_model_solver_support,
)


EXACT_PRIORITY = ("z3", "cvc5", "yices")
_MARKER = "STLMC_RUNTIME_PROBE="


def _nonlinear(expression):
    if isinstance(expression, Dynamics):
        return any(_nonlinear(child) or (
            isinstance(expression, Ode) and bool(get_vars(child))
        ) for child in expression.exps)
    if isinstance(expression, Mul) and get_vars(expression.left) and get_vars(expression.right):
        return True
    if isinstance(expression, Div) and get_vars(expression.right):
        return True
    if isinstance(expression, Pow) and get_vars(expression.left):
        try:
            if Fraction(str(expression.right.value)) not in (0, 1):
                return True
        except (AttributeError, ValueError, ZeroDivisionError):
            return True
    if isinstance(expression, Unary):
        return _nonlinear(expression.child)
    if isinstance(expression, Binary):
        return _nonlinear(expression.left) or _nonlinear(expression.right)
    if isinstance(expression, Multinary):
        return any(_nonlinear(child) for child in expression.children)
    return False


def _requires_nonlinear_logic(model, goals, definitions):
    expressions = [model.init, *model.const_dict.values()]
    for module in model.modules:
        expressions.extend([module["mode"], module["inv"], module["flow"]])
        for guard, reset in module["jump"].items():
            expressions.extend([guard, reset])
    expressions.extend(substitution(goal.get_formula(), definitions) for goal in goals)
    return any(_nonlinear(expression) for expression in expressions)


def solver_candidates(model, goals, definitions):
    """Use dReal for evolving-state ODEs and dReal-only arithmetic.

    Autonomous state-independent derivatives can be lowered exactly by the
    algebraic adapters. A general ODE must never use their endpoint lowering.
    """
    native_ode = any(
        isinstance(module["flow"], Ode) and any(
            get_vars(expression) & set(module["flow"].vars) or any(
                variable.id in {"t", "time"} or variable.id.startswith("tau_")
                for variable in get_vars(expression)
            )
            for expression in module["flow"].exps
        )
        for module in model.modules
    )
    requires_dreal = native_ode or model_requires_dreal(model) or any(
        expression_requires_dreal(substitution(goal.get_formula(), definitions))
        for goal in goals
    )
    return ("dreal",) if requires_dreal else EXACT_PRIORITY + ("dreal",)


def _probe_child(name, sections):
    """Executed in one disposable process; no installer version policy."""
    from ..objects.configuration import Configuration, Section
    from .solver_factory import SolverFactory

    configuration = Configuration()
    for section_name, arguments in sections.items():
        section = Section()
        section.name = section_name
        section.arguments = arguments
        configuration.add_section(section)
    configuration.get_section("common").arguments["solver"] = name
    configuration.get_section("common").arguments["save-smt2"] = "false"
    try:
        solver = SolverFactory().generate_solver(configuration)
        if name != "dreal":
            from ..constraints.constraints import Eq, Real, RealVal
            from .abstract_solver import SolverStatus
            result = solver.solve(Eq(Real("stlmc_runtime_probe"), RealVal("1")), timeout=5)
            if result.status is not SolverStatus.SAT:
                raise SolverUnavailableError("basic SAT probe returned {}".format(result.status))
        # The dReal factory performs native ODE/invariant regression probes.
        response = {"available": True, "detail": "runtime capability check passed"}
    except Exception as error:
        response = {"available": False, "detail": str(error)}
    print(_MARKER + json.dumps(response), flush=True)


def _stop_probe(process):
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGKILL)
        else:
            process.kill()
    except ProcessLookupError:
        pass
    process.communicate()


def probe_solver_runtime(name, configuration):
    """Bound native initialization and isolate Yices/CVC5 import lifetimes."""
    if name == "dreal":
        # The validator already isolates and reaps each native subprocess.
        # Do not put that supervisor inside another killable probe process:
        # its native child has its own process group and could outlive it.
        from .dreal_runtime import validate_dreal_runtime
        try:
            executable = configuration.get_section("dreal").get_value("executable-path")
            if executable == "dReal":
                executable = find_dreal() or executable
            metadata = validate_dreal_runtime(executable)
            return True, "native runtime capability check passed ({})".format(metadata["version"])
        except (SolverUnavailableError, ElementNotFoundError, OSError) as error:
            return False, str(error)
    sections = {
        key: dict(section.arguments)
        for key, section in configuration.sections_by_name.items()
    }
    environment = dict(os.environ)
    source_root = str(Path(__file__).resolve().parents[2])
    environment["PYTHONPATH"] = source_root + os.pathsep + environment.get("PYTHONPATH", "")
    script = (
        "import json,sys; from stlmc.solver.auto_selection import _probe_child; "
        "_probe_child(sys.argv[1],json.loads(sys.argv[2]))"
    )
    try:
        process = subprocess.Popen(
            [sys.executable, "-c", script, name, json.dumps(sections)],
            env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, start_new_session=(os.name == "posix"),
        )
        try:
            stdout, stderr = process.communicate(timeout=25)
        except subprocess.TimeoutExpired:
            _stop_probe(process)
            return False, "runtime probe timed out"
        except BaseException:
            _stop_probe(process)
            raise
        if process.returncode:
            return False, "runtime probe exited {}: {}".format(process.returncode, stderr[-1000:].strip())
        lines = [line[len(_MARKER):] for line in stdout.splitlines() if line.startswith(_MARKER)]
        if len(lines) != 1:
            return False, "runtime probe returned no unique capability report"
        response = json.loads(lines[0])
        if not isinstance(response, dict) or type(response.get("available")) is not bool:
            return False, "invalid runtime capability report"
        return response["available"], str(response.get("detail", ""))
    except (OSError, ValueError, TypeError) as error:
        return False, "runtime probe failed: {}".format(error)


def select_available_solver(model, goals, definitions, configuration, probe=None):
    """Choose the first supported, installed runtime; never silently install."""
    probe = probe or probe_solver_runtime
    goals = tuple(goals)
    reasons = []
    candidates = solver_candidates(model, goals, definitions)
    nonlinear = _requires_nonlinear_logic(model, goals, definitions)
    for name in candidates:
        try:
            if name != "dreal":
                logic = configuration.get_section(name).get_value("logic").upper()
                if nonlinear and logic in {"LRA", "QF_LRA"}:
                    reasons.append("{}: requested {} cannot represent this nonlinear encoding".format(name, logic))
                    continue
            validate_model_solver_support(name, model)
            for goal in goals:
                validate_formula_solver_support(name, substitution(goal.get_formula(), definitions))
        except (NotSupportedError, ElementNotFoundError) as error:
            reasons.append("{}: {}".format(name, error))
            continue
        available, detail = probe(name, configuration)
        if available:
            return name
        reasons.append("{}: {}".format(name, detail))
    raise SolverUnavailableError(
        "auto could not find a supported, usable solver.\n  {}\n"
        "Check solver installations with stlmc-installer check --solver {}. "
        "Install supported solver packages with stlmc-installer install --solver {}. "
        "dReal additionally requires a compatible native build; use -executable-path /path/to/dReal."
        .format("\n  ".join(reasons), " ".join(candidates), " ".join(candidates))
    )
