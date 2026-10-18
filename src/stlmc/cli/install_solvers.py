"""Install or check STLMC's solver prerequisites."""

import argparse
import hashlib
import importlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.request
import zipfile
from pathlib import Path
from importlib.metadata import version

from ..solver.availability import find_dreal, user_dreal_path, load_yices_binding
from .dependency_policy import (
    DREAL_VERSION as _DREAL_VERSION, Z3_PACKAGE as _Z3_PACKAGE,
    CVC5_PACKAGE as _CVC5_PACKAGE, YICES_PACKAGE as _YICES_PACKAGE,
    YICES_NATIVE_VERSION,
    DREAL_ARCHIVE_SHA256,
)


def _python_package_status(module_name, distribution_name, package_spec, detail):
    expected = package_spec.rsplit("==", 1)[1]
    try:
        importlib.import_module(module_name)
        installed = version(distribution_name)
    except Exception as error:
        return False, str(error)
    if installed != expected:
        return False, "installed {}, expected {}".format(installed, expected)
    return True, "{} ({})".format(detail, installed)


def _probe_one(name):
    if name == "cvc5":
        return _python_package_status(
            "cvc5", "cvc5", _CVC5_PACKAGE, "Python package available"
        )
    if name == "z3":
        return _python_package_status(
            "z3", "z3-solver", _Z3_PACKAGE, "Python package available"
        )
    try:
        yices_module = load_yices_binding()
        available, detail = _python_package_status(
            "yices", "yices", _YICES_PACKAGE,
            "Python binding and native library available",
        )
        if available:
            native_version = yices_module.Yices.version
            if isinstance(native_version, bytes):
                native_version = native_version.decode("ascii")
            if str(native_version) != YICES_NATIVE_VERSION:
                return False, (
                    "native Yices {}, expected {}. System packages are not "
                    "automatically downgraded; use stlmc-installer install --solver yices "
                    "--build for a managed build."
                ).format(native_version, YICES_NATIVE_VERSION)
            detail = "{}, native {}, thread_safe={}, mcsat={}".format(
                detail, native_version,
                bool(yices_module.Yices.is_thread_safe()),
                bool(yices_module.Yices.has_mcsat()),
            )
        return available, detail
    except Exception as error:
        return False, str(error).splitlines()[-1]


def _backend_status(name):
    # Native CVC5 and Yices may conflict when initialized in one process.
    # Each probe has one backend and can also contain a native import crash.
    environment = dict(os.environ)
    source_root = str(Path(__file__).resolve().parents[2])
    environment["PYTHONPATH"] = source_root + os.pathsep + environment.get("PYTHONPATH", "")
    script = "import json,sys; from stlmc.cli.install_solvers import _probe_one; print(json.dumps(_probe_one(sys.argv[1])))"
    try:
        probe = subprocess.run([sys.executable, "-c", script, name], env=environment,
                               capture_output=True, text=True, timeout=30)
        if probe.returncode != 0:
            return False, "probe exit {}: {}".format(probe.returncode, probe.stderr.strip())
        available, detail = json.loads(probe.stdout)
        return bool(available), str(detail)
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        return False, "probe failed: " + str(error)


def _status():
    result = {name: _backend_status(name) for name in ("cvc5", "z3", "yices")}

    dreal = find_dreal()
    if dreal:
        result["dreal"] = _dreal_status(dreal)
    else:
        result["dreal"] = (False, "dReal executable not found")
    return result


def _dreal_status(executable):
    """Read-only, timeout-bounded native version and SMT smoke checks."""
    deadline = time.monotonic() + 10
    def remaining():
        timeout = deadline - time.monotonic()
        if timeout <= 0:
            raise subprocess.TimeoutExpired(str(executable), 10)
        return timeout
    try:
        result = subprocess.run([str(executable), "--version"],
                                capture_output=True, text=True, timeout=remaining())
        output = result.stdout + result.stderr
        match = re.search(r"\bdReal\s+v?(\d+(?:\.\d+){2,3})\b", output)
        actual = match.group(1) if match else "unrecognized"
        if result.returncode != 0 or actual != _DREAL_VERSION:
            return False, "{}: dReal version {}, expected {}".format(
                executable, actual, _DREAL_VERSION)
        with tempfile.TemporaryDirectory(prefix="stlmc-dreal-check-") as directory:
            query = Path(directory) / "smoke.smt2"
            algebraic = ("(set-logic QF_NRA)\n(declare-fun x () Real)\n"
                         "(assert (= x 1))\n(check-sat)\n(exit)\n")
            # x(t)=t-t^2: both endpoints are zero, interior maximum is 1/4.
            # The UNSAT query checks forall_t in the interior, not just bounds.
            ode = """(set-logic QF_NRA_ODE)
(declare-fun time_0 () Real [1, 1])
(declare-fun x () Real [-2, 2])
(declare-fun v () Real [-2, 2])
(declare-fun x_0_0 () Real [0, 0])
(declare-fun v_0_0 () Real [1, 1])
(declare-fun x_0_t () Real [-2, 2])
(declare-fun v_0_t () Real [-2, 2])
(define-ode flow_1 ((= d/dt[x] v) (= d/dt[v] (- 0 2))))
(assert (= [x_0_t v_0_t] (integral 0. time_0 [x_0_0 v_0_0] flow_1)))
(assert (forall_t 1 [0 time_0] (< x_0_t {limit})))
(check-sat)
(exit)
"""
            for label, formula, expected in (
                    ("algebraic SAT", algebraic, r"(?:delta-sat|sat)"),
                    ("ODE SAT", ode.format(limit="0.5"), r"(?:delta-sat|sat)"),
                    ("ODE interior UNSAT", ode.format(limit="0.1"), "unsat")):
                query.write_text(formula, encoding="utf-8")
                result = subprocess.run(
                    [str(executable), "--precision", "0.000001", "--ode-step", "0.01", str(query)],
                    capture_output=True, text=True, timeout=remaining())
                if result.returncode != 0 or not re.search(
                        r"(?m)^\s*" + expected + r"\b", result.stdout):
                    return False, "{}: dReal {} smoke check failed (exit {}): {}".format(
                        executable, label, result.returncode, (result.stdout + result.stderr).strip())
        return True, "{} (dReal {}; SMT smoke check passed)".format(executable, actual)
    except (OSError, subprocess.SubprocessError) as error:
        return False, "{}: dReal probe failed: {}".format(executable, error)


def _run(command):
    print("+ {}".format(" ".join(command)), flush=True)
    subprocess.run(command, check=True)


def _install_yices():
    if sys.platform == "darwin":
        if shutil.which("brew") is None:
            raise RuntimeError("Homebrew is required to install Yices on macOS")
        _run(["brew", "install", "SRI-CSL/sri-csl/yices2"])
    elif sys.platform.startswith("linux"):
        if shutil.which("apt-get") is None:
            raise RuntimeError(
                "automatic Yices installation supports Ubuntu/Debian only; "
                "install libyices with your system package manager"
            )
        _run(["sudo", "add-apt-repository", "-y", "ppa:sri-csl/formal-methods"])
        _run(["sudo", "apt-get", "update"])
        _run(["sudo", "apt-get", "install", "-y", "yices2", "yices2-dev"])
        _run(["sudo", "ldconfig"])
    else:
        raise RuntimeError("automatic Yices installation is not supported on this OS")


def _install_python_package(package):
    _run([sys.executable, "-m", "pip", "install", "--upgrade", package])


def _verify_dreal_archive(path, name):
    expected = DREAL_ARCHIVE_SHA256[name]
    digest = hashlib.sha256()
    with open(path, "rb") as archive:
        for chunk in iter(lambda: archive.read(1024 * 1024), b""):
            digest.update(chunk)
    if digest.hexdigest() != expected:
        raise RuntimeError("dReal archive SHA256 mismatch for {}; installation unchanged".format(name))


def _install_dreal():
    if sys.platform == "darwin":
        archive_name = "dReal-{}-darwin.zip".format(_DREAL_VERSION)
        member = "dReal-{}-darwin/bin/dReal".format(_DREAL_VERSION)
        archive_kind = "zip"
    elif sys.platform.startswith("linux") and os.uname().machine in {
        "x86_64", "amd64"
    }:
        archive_name = "dReal-{}-linux.tar.gz".format(_DREAL_VERSION)
        member = "dReal-{}-linux/bin/dReal".format(_DREAL_VERSION)
        archive_kind = "tar"
    else:
        raise RuntimeError(
            "automatic dReal installation supports macOS and x86_64 Linux only"
        )

    url = "https://github.com/dreal/dreal3/releases/download/v{}/{}".format(
        _DREAL_VERSION, archive_name
    )
    destination = user_dreal_path()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="stlmc-dreal-install-") as directory:
        archive_path = os.path.join(directory, archive_name)
        print("Downloading {}".format(url), flush=True)
        urllib.request.urlretrieve(url, archive_path)
        _verify_dreal_archive(archive_path, archive_name)
        if archive_kind == "zip":
            with zipfile.ZipFile(archive_path) as archive:
                content = archive.read(member)
        else:
            with tarfile.open(archive_path, "r:gz") as archive:
                extracted = archive.extractfile(member)
                if extracted is None:
                    raise RuntimeError("dReal executable is missing from the archive")
                content = extracted.read()
        with tempfile.TemporaryDirectory(prefix=".stlmc-dreal-", dir=str(destination.parent)) as staging:
            temporary = Path(staging) / "dReal"
            temporary.write_bytes(content)
            temporary.chmod(0o755)
            available, detail = _dreal_status(str(temporary))
            if not available:
                raise RuntimeError("downloaded dReal failed validation: " + detail)
            os.replace(str(temporary), str(destination))
    print("Installed dReal at {}".format(destination))


def build_parser():
    parser = argparse.ArgumentParser(
        description=(
            "Install and verify the external solver prerequisites used by STLMC.\n"
            "Without --check, only missing components are installed."
        ),
        epilog=(
            "Solvers:\n"
            "  all    Check or install CVC5, Z3, Yices, and dReal (default).\n"
            "  cvc5   Install the cvc5 Python package.\n"
            "  z3     Install the z3-solver Python package.\n"
            "  yices  Install the Python binding and native Yices library.\n"
            "  dreal  Install the dReal 3 executable in the user solver directory.\n"
            "\n"
            "dReal lookup order:\n"
            "  1. ~/Library/Application Support/stlmc/solvers/dReal3/dReal (macOS), or\n"
            "     $XDG_DATA_HOME/stlmc/solvers/dReal3/dReal, or\n"
            "     ~/.local/share/stlmc/solvers/dReal3/dReal (Linux).\n"
            "  2. An executable named dReal in PATH.\n"
            "  Explicit -executable-path settings take precedence.\n"
            "\n"
            "Automatic native installation:\n"
            "  Yices: Ubuntu/Debian through apt, or macOS through Homebrew.\n"
            "  dReal: macOS or x86-64 Linux.\n"
            "  Native package installation may request administrator privileges.\n"
            "\n"
            "Homebrew 6 first-time Yices setup:\n"
            "  Third-party formula trust may be required before installation:\n"
            "  brew tap SRI-CSL/sri-csl\n"
            "  brew trust --formula sri-csl/sri-csl/yices2\n"
            "  brew trust --formula sri-csl/sri-csl/libpoly\n"
            "  brew trust --formula sri-csl/sri-csl/cudd\n"
            "  Trusting the entire SRI tap is not required.\n"
            "  If Apple Silicon cannot find libyices.dylib, run:\n"
            "  export DYLD_LIBRARY_PATH=\"$(brew --prefix)/lib\"\n"
            "\n"
            "Examples:\n"
            "  stlmc-installer install --solver all\n"
            "  stlmc-installer install --solver dreal\n"
            "  stlmc-installer check --solver yices\n"
            "  stlmc-installer check --solver all"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "solver", nargs="?", default="all",
        choices=("all", "cvc5", "z3", "yices", "dreal"),
        help="solver to install or check (default: all)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="report availability without downloading or installing anything",
    )
    return parser


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)

    selected = (("cvc5", "z3", "yices", "dreal")
                if args.solver == "all" else (args.solver,))
    before = _status()
    if not args.check:
        if "cvc5" in selected and not before["cvc5"][0]:
            _install_python_package(_CVC5_PACKAGE)
        if "z3" in selected and not before["z3"][0]:
            _install_python_package(_Z3_PACKAGE)
        if "yices" in selected and not before["yices"][0]:
            _install_python_package(_YICES_PACKAGE)
            _install_yices()
        if "dreal" in selected and not before["dreal"][0]:
            _install_dreal()

    status = _status()
    failed = False
    for name in selected:
        available, detail = status[name]
        print("{:<6}: {} ({})".format(
            name, "available" if available else "unavailable", detail
        ))
        failed = failed or not available
    return 1 if failed else 0
