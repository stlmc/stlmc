"""Bounded, feature-based validation of an external dReal3 ODE runtime.

Version strings alone do not establish ODE correctness: an older dReal3
silently drops forall_t invariants on zero-derivative state variables. These
small probes detect that failure, not arbitrary solver unsoundness.
"""

import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import threading
import warnings

from ..exceptions import SolverUnavailableError
from ..cli.dependency_policy import DREAL_VERSION, DREAL_KNOWN_LIMITATIONS_WARNING


_PROBE_TIMEOUT = 5
_SUCCESS_CACHE = {}
_CACHE_LOCK = threading.RLock()
_HINT = (
    "Use a compatible dReal3 build with native ODE and zero-derivative "
    "forall_t support; select it with -executable-path /path/to/dReal."
)

# The clock's nonzero derivative ensures this actually executes native ODE
# integration even though g is constant. All comparisons have a 0.5 margin,
# much larger than delta, so an incorrect result is not a boundary ambiguity.
_ODE_QUERY = """(set-logic QF_NRA_ODE)
(declare-fun time_0 () Real [3,3])
(declare-fun g () Real [-10,10])
(declare-fun g_0_0 () Real [8,8])
(declare-fun g_0_t () Real [-10,10])
(declare-fun clock () Real [0,10])
(declare-fun clock_0_0 () Real [0,0])
(declare-fun clock_0_t () Real [0,10])
(define-ode flow_1 ((= d/dt[g] 0) (= d/dt[clock] 1)))
(assert (= [g_0_t clock_0_t]
           (integral 0. time_0 [g_0_0 clock_0_0] flow_1)))
(assert (forall_t 1 [0 time_0] (< g_0_t LIMIT)))
(check-sat)
(exit)
"""


def _run_bounded(command):
    """Execute one native probe, killing/reaping its process group on timeout."""
    process = subprocess.Popen(
        command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, encoding="utf-8", errors="replace",
        start_new_session=(os.name == "posix"),
    )
    try:
        stdout, stderr = process.communicate(timeout=_PROBE_TIMEOUT)
    except BaseException:
        # Also clean up if interrupted by the caller, not only on a timeout.
        try:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL)
            else:
                process.kill()
        except ProcessLookupError:
            pass
        finally:
            process.communicate()
        raise
    return process.returncode, stdout, stderr


def _signature(path):
    stat = path.stat()
    return (str(path), stat.st_dev, stat.st_ino, stat.st_mtime_ns, stat.st_size)


def _model_value(stdout, name, expected):
    match = re.search(
        r"^" + re.escape(name) + r"\s*:.*=\s*\[\s*([^,\]]+)\s*,\s*([^\]]+)\s*\]\s*$",
        stdout, re.MULTILINE,
    )
    if match is None:
        return False
    try:
        lower, upper = (float(part) for part in match.groups())
        return (lower <= expected <= upper
                and abs(lower - expected) <= 1e-4
                and abs(upper - expected) <= 1e-4)
    except (ValueError, OverflowError):
        return False


def validate_dreal_runtime(executable):
    """Return capability metadata, or raise ``SolverUnavailableError``.

    No installation, configuration, or executable is modified. Three child
    processes have independent five-second limits. Only successful results
    are cached, keyed by resolved executable and its filesystem identity.
    The probes are necessary capability checks, not a correctness certificate
    for every query accepted by a solver build.
    """
    try:
        raw = os.fspath(executable)
        if not raw:
            raise ValueError("no executable was selected")
        candidate = shutil.which(raw) if os.path.dirname(raw) == "" else raw
        if candidate is None:
            raise ValueError("executable was not found")
        path = Path(candidate).expanduser().resolve(strict=True)
        if not path.is_file() or not os.access(str(path), os.X_OK):
            raise ValueError("selected path is not an executable file")
        key = _signature(path)
    except (OSError, TypeError, ValueError) as error:
        raise SolverUnavailableError("dReal runtime unavailable: {}. {}".format(error, _HINT)) from error

    with _CACHE_LOCK:
        cached = _SUCCESS_CACHE.get(key)
        if cached is not None:
            return dict(cached)
        stage = "version"
        zero_derivative_forall = True
        known_limitations = None
        try:
            code, stdout, stderr = _run_bounded([str(path), "--version"])
            version = (stdout + "\n" + stderr).strip()
            if code != 0 or re.search(r"\bdReal\s+v?3\.", version, re.IGNORECASE) is None:
                raise ValueError("expected a dReal3 executable, got {!r}".format(version[:240]))
            version_token = re.search(r"\bdReal\s+v?([^\s(]+)", version, re.IGNORECASE)
            official_release = bool(version_token and version_token.group(1) == DREAL_VERSION)
            with tempfile.TemporaryDirectory(prefix="stlmc-dreal-runtime-") as directory:
                for name, limit, expected in [("positive", "8.5", "sat"), ("negative", "7.5", "unsat")]:
                    stage = "{} zero-derivative forall_t ODE probe".format(name)
                    query = Path(directory) / (name + ".smt2")
                    query.write_text(_ODE_QUERY.replace("LIMIT", limit), encoding="utf-8")
                    code, stdout, stderr = _run_bounded([
                        str(path), str(query), "--precision", "0.000001", "--short_sat", "--model",
                    ])
                    if code != 0:
                        raise ValueError("native exit {}: {}".format(code, (stderr or stdout)[-400:]))
                    has_sat = re.search(r"^delta-sat\b", stdout, re.MULTILINE) is not None
                    has_unsat = re.search(r"^\s*unsat\s*$", stdout, re.MULTILINE) is not None
                    if expected == "sat":
                        if (not has_sat or has_unsat
                                or not _model_value(stdout, "g_0_t", 8.0)
                                or not _model_value(stdout, "clock_0_t", 3.0)):
                            raise ValueError("expected SAT with integrated model g=8, clock=3")
                    elif not has_unsat or has_sat:
                        # Only the explicitly supported official release's
                        # reproduced defect is warn-and-allow. A crash, a
                        # missing/wrong integrated model or ambiguous output
                        # must never be reclassified as that known defect.
                        statuses = [line.strip() for line in stdout.splitlines()
                                    if re.match(r"^\s*(?:delta-sat|sat|unsat|unknown)\b", line)]
                        valid_sat_status = (len(statuses) == 1 and re.fullmatch(
                            r"delta-sat(?:\s+with\s+delta\s*=\s*[0-9]+(?:\.[0-9]*)?(?:[eE][+-]?[0-9]+)?)?",
                            statuses[0]) is not None)
                        if (official_release and has_sat and not has_unsat
                                and valid_sat_status and not stderr.strip()
                                and not re.search(r"^\s*(?:error|exception|fatal)\b", stdout, re.I | re.M)
                                and _model_value(stdout, "g_0_t", 8.0)
                                and _model_value(stdout, "clock_0_t", 3.0)):
                            zero_derivative_forall = False
                            known_limitations = DREAL_KNOWN_LIMITATIONS_WARNING
                        else:
                            raise ValueError("expected UNSAT; this build may ignore invariants on zero-derivative parameters")
            if key != _signature(path):
                raise ValueError("executable changed during validation; retry with a stable executable")
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            raise SolverUnavailableError(
                "dReal runtime failed {}: {}. {}".format(stage, error, _HINT)
            ) from error
        result = {"executable": str(path), "version": version,
                  "ode_supported": True, "zero_derivative_forall": zero_derivative_forall,
                  "known_limitations": known_limitations}
        # Drop obsolete entries for this path, while allowing different builds
        # in the same process. Failed probes never enter the cache.
        for previous in list(_SUCCESS_CACHE):
            if previous[0] == str(path):
                del _SUCCESS_CACHE[previous]
        if known_limitations:
            warnings.warn(known_limitations, RuntimeWarning, stacklevel=2)
        _SUCCESS_CACHE[key] = result
        return dict(result)
