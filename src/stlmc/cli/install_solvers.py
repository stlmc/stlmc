"""Install or check STLMC's solver prerequisites."""

import argparse
import importlib
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
import zipfile
from importlib.metadata import PackageNotFoundError, version

from ..solver.availability import find_dreal, user_dreal_path


_DREAL_VERSION = "3.16.06.02"
_Z3_PACKAGE = "z3-solver==4.15.4.0"
_CVC5_PACKAGE = "cvc5==1.3.4"
_YICES_PACKAGE = "yices==1.1.6"


def _python_package_status(module_name, distribution_name, package_spec, detail):
    expected = package_spec.rsplit("==", 1)[1]
    try:
        importlib.import_module(module_name)
        installed = version(distribution_name)
    except (ImportError, OSError, PackageNotFoundError) as error:
        return False, str(error)
    if installed != expected:
        return False, "installed {}, expected {}".format(installed, expected)
    return True, "{} ({})".format(detail, installed)


def _status():
    result = {}
    result["cvc5"] = _python_package_status(
        "cvc5", "cvc5", _CVC5_PACKAGE, "Python package available"
    )
    result["z3"] = _python_package_status(
        "z3", "z3-solver", _Z3_PACKAGE, "Python package available"
    )
    try:
        yices_module = importlib.import_module("yices")
        available, detail = _python_package_status(
            "yices", "yices", _YICES_PACKAGE,
            "Python binding and native library available",
        )
        if available:
            detail = "{}, native {}".format(
                detail, yices_module.Yices.version
            )
        result["yices"] = available, detail
    except Exception as error:
        result["yices"] = (False, str(error).splitlines()[-1])

    dreal = find_dreal()
    if dreal:
        result["dreal"] = (True, dreal)
    else:
        result["dreal"] = (False, "dReal executable not found")
    return result


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
        if archive_kind == "zip":
            with zipfile.ZipFile(archive_path) as archive:
                content = archive.read(member)
        else:
            with tarfile.open(archive_path, "r:gz") as archive:
                extracted = archive.extractfile(member)
                if extracted is None:
                    raise RuntimeError("dReal executable is missing from the archive")
                content = extracted.read()
        temporary = destination.with_suffix(".tmp")
        temporary.write_bytes(content)
        temporary.chmod(0o755)
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
            "  1. An executable named dReal in PATH.\n"
            "  2. ~/Library/Application Support/stlmc/solvers/dReal3/dReal (macOS).\n"
            "  3. $XDG_DATA_HOME/stlmc/solvers/dReal3/dReal, or\n"
            "     ~/.local/share/stlmc/solvers/dReal3/dReal (Linux).\n"
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
            "  stlmc-install-solvers\n"
            "  stlmc-install-solvers dreal\n"
            "  stlmc-install-solvers yices --check\n"
            "  stlmc-install-solvers --check"
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


def main():
    parser = build_parser()
    args = parser.parse_args()

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


if __name__ == "__main__":
    raise SystemExit(main())
