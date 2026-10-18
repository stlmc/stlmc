"""Component installer; native source builds never overwrite system libraries."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
import uuid

from . import install_solvers as solvers
from .dependency_policy import (
    YICES_NATIVE_VERSION, YICES_SOURCE_SHA256, YICES_SOURCE_URL,
    visualization_packages,
)
from ..solver.availability import solver_data_dir
from ..exceptions import SolverUnavailableError
from .native_linkage import audit_static_linkage

YICES_VERSION = YICES_NATIVE_VERSION
YICES_SOURCE = YICES_SOURCE_URL
YICES_SHA256 = YICES_SOURCE_SHA256
VISUALIZE_PACKAGES = visualization_packages((3, 10))


def _probe_library(library):
    # A subprocess avoids keeping an old library/binding loaded during activation.
    script = """import ctypes,json,sys
l=ctypes.CDLL(sys.argv[1]); l.yices_init()
try:
 print(json.dumps(dict(version=ctypes.c_char_p.in_dll(l,'yices_version').value.decode(),
 thread_safe=bool(l.yices_is_thread_safe()),mcsat=bool(l.yices_has_mcsat()))))
finally: l.yices_exit()
"""
    result = subprocess.run([sys.executable, "-c", script, str(library)],
                            check=True, capture_output=True, text=True, timeout=30)
    return json.loads(result.stdout)


def _extract_source(archive, destination):
    with tarfile.open(archive, "r:gz") as source:
        members = source.getmembers()
        base = destination.resolve()
        for member in members:
            target = (base / member.name).resolve()
            if (target != base and base not in target.parents) or not (
                    member.isdir() or member.isfile()):
                raise RuntimeError("Unsafe Yices source archive member: " + member.name)
        source.extractall(str(base), members=members)
    roots = list(destination.iterdir())
    if len(roots) != 1 or not roots[0].is_dir():
        raise RuntimeError("Expected one Yices source directory")
    return roots[0]


def _logged(command, cwd, environment, log):
    with log.open("a") as output:
        output.write("+ " + shlex.join([str(x) for x in command]) + "\n")
        output.flush()
        subprocess.run([str(x) for x in command], cwd=str(cwd), env=environment,
                       stdout=output, stderr=subprocess.STDOUT, check=True)


def build_yices(*, prefix=None, source=None, thread_safe=False, mcsat=True, jobs=1):
    if jobs < 1:
        raise RuntimeError("--jobs must be a positive build-job count")
    if sys.platform != "darwin" and not sys.platform.startswith("linux"):
        raise RuntimeError("Yices source builds support Linux and macOS")
    tools = ["make", "gperf", "sed", shlex.split(os.environ.get("CC", "cc"))[0]]
    missing = [tool for tool in tools if shutil.which(tool) is None]
    if missing:
        raise RuntimeError("Missing Yices build tools: {}. Install a C99 compiler, GNU make, "
                           "gperf and sed; GMP development files are also required. "
                           "No system packages were installed.".format(", ".join(missing)))
    base = Path(prefix).expanduser().resolve() if prefix else solver_data_dir() / "yices"
    if not prefix and any(c.isspace() for c in str(base)):
        base = Path.home() / ".local" / "share" / "stlmc" / "yices"
    if any(c.isspace() for c in str(base)):
        raise RuntimeError("Yices make requires a --prefix path without whitespace")
    if base in [Path("/"), Path("/usr"), Path("/usr/local"), Path("/opt"), Path.home()]:
        raise RuntimeError("Choose a dedicated user-owned --prefix directory")
    build = base / "builds" / ("yices-" + YICES_VERSION + "-" + uuid.uuid4().hex)
    installed = build / "prefix"
    build.mkdir(parents=True, exist_ok=False)
    log = build / "build.log"
    environment = dict(os.environ)
    flags = environment.get("LDFLAGS", "")
    # configure uses this absolute prefix for install names and ELF rpaths.
    environment["LDFLAGS"] = flags + " -Wl,-rpath," + str(installed / "lib")
    try:
        with tempfile.TemporaryDirectory(prefix="stlmc-yices-source-") as temporary:
            temporary = Path(temporary)
            if source:
                source = Path(source).expanduser().resolve()
                if not source.is_dir():
                    raise RuntimeError("--source must name a Yices source directory")
                work = temporary / "source"
                shutil.copytree(str(source), str(work), symlinks=False)
            else:
                archive = temporary / "source.tar.gz"
                urllib.request.urlretrieve(YICES_SOURCE, str(archive))
                if hashlib.sha256(archive.read_bytes()).hexdigest() != YICES_SHA256:
                    raise RuntimeError("Yices source checksum mismatch; refusing to build")
                work = _extract_source(archive, temporary / "unpacked")
            if not (work / "configure").is_file():
                if shutil.which("autoconf") is None:
                    raise RuntimeError("autoconf is required to build the official Git source")
                _logged(["autoconf"], work, environment, log)
            command = [str(work / "configure"), "--prefix=" + str(installed),
                       "--enable-mcsat" if mcsat else "--disable-mcsat"]
            if thread_safe:
                command.append("--enable-thread-safety")
            _logged(command, work, environment, log)
            _logged(["make", "-j", str(jobs)], work, environment, log)
            _logged(["make", "install"], work, environment, log)
        candidates = sorted((installed / "lib").glob("libyices*.dylib")) + sorted(
            (installed / "lib").glob("libyices.so*"))
        if not candidates:
            raise RuntimeError("Build did not install a shared libyices library")
        library = candidates[0].resolve()
        capabilities = _probe_library(library)
        if capabilities.get("version") != YICES_VERSION or (
                thread_safe and not capabilities.get("thread_safe")) or (
                mcsat and not capabilities.get("mcsat")):
            raise RuntimeError("Installed Yices failed capability verification: " +
                               json.dumps(capabilities))
        if not mcsat and capabilities.get("mcsat"):
            raise RuntimeError("--without-mcsat build unexpectedly reports MCSAT support")
        metadata = dict(capabilities, library=str(library), prefix=str(installed),
                        build_jobs=jobs, source=YICES_SOURCE if not source else str(source))
        activation = solver_data_dir() / "yices" / "active.json"
        activation.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(mode="w", dir=str(activation.parent),
                                         prefix="activate-", delete=False) as output:
            json.dump(metadata, output, indent=2)
            replacement = Path(output.name)
        try:
            os.replace(str(replacement), str(activation))
        finally:
            if replacement.exists():
                replacement.unlink()
        print("Activated Yices {}: thread_safe={}, mcsat={} ({})".format(
            YICES_VERSION, capabilities["thread_safe"], capabilities["mcsat"], library))
        if not mcsat:
            print("LRA/core-only installation: final nonlinear arithmetic requires MCSAT.")
        return metadata
    except (OSError, subprocess.SubprocessError, ValueError, RuntimeError) as error:
        raise RuntimeError(
            "Yices build/probe failed; previous installation remains active. {}. "
            "Log: {}. Prerequisites: C99 compiler, GNU make, gperf, sed, autoconf "
            "(Git source), GMP headers/library; MCSAT additionally needs libpoly "
            "and PIC CUDD headers/libraries. Set CPPFLAGS/LDFLAGS for user dependency "
            "prefixes. No OS packages were installed.".format(error, log)) from error


def build_dreal(*, prefix=None, jobs=1):
    """Build privately and atomically activate only a validated executable."""
    if not isinstance(jobs, int) or jobs < 1:
        raise RuntimeError("--jobs must be a positive build-job count")
    base = (Path(prefix).expanduser() if prefix else solver_data_dir() / "dReal3").resolve()
    protected = (Path.home().resolve(), Path(__file__).resolve().parents[3])
    if base in (Path("/"), Path("/usr"), Path("/usr/local"), Path("/opt")) or any(
            base == path or base in path.parents for path in protected):
        raise RuntimeError("Choose a dedicated user-owned --prefix directory")
    build = base / "builds" / ("dreal-" + uuid.uuid4().hex)
    destination = build / "prefix"
    try:
        from .dreal_build import build_dreal as build_private_dreal

        build.mkdir(parents=True, exist_ok=False)
        executable = Path(build_private_dreal(destination, jobs=jobs)).resolve()
        expected = (destination / "bin" / "dReal").resolve()
        if (executable != expected or destination.resolve() not in executable.parents
                or not executable.is_file()):
            raise RuntimeError("dReal builder did not return its private bin/dReal")
        target = solvers.user_dreal_path()
        target.parent.mkdir(parents=True, exist_ok=True)
        # Stage next to the active path so os.replace stays atomic even when
        # --prefix selects another filesystem. No existing file is truncated.
        with tempfile.TemporaryDirectory(prefix="activate-dreal-", dir=str(target.parent)) as staging:
            staged = Path(staging) / "dReal"
            shutil.copy2(str(executable), str(staged))
            staged.chmod(staged.stat().st_mode | 0o111)
            # Audit and execute the exact bytes that will become active, not
            # a mutable source file or another PATH binary.
            linkage = audit_static_linkage(staged)
            metadata = solvers.validate_dreal_runtime(staged)
            os.replace(str(staged), str(target))
    except (ImportError, OSError, RuntimeError, subprocess.SubprocessError, ValueError,
            SolverUnavailableError) as error:
        raise RuntimeError(
            "dReal private build/validation failed; previous installation remains active. "
            "{}. Build prefix: {}. No OS packages were installed.".format(error, destination)
        ) from error
    result = dict(metadata, executable=str(target), prefix=str(destination),
                  build_jobs=jobs, linkage=dict(linkage, executable=str(target)))
    print("Activated private dReal build: {} (build prefix: {})".format(target, destination))
    return result


def visualize_status(modules=None):
    status = {}
    packages = visualization_packages(sys.version_info)
    for module in (packages if modules is None else modules):
        try:
            with tempfile.TemporaryDirectory(prefix="stlmc-visual-check-") as temporary:
                environment = dict(os.environ, MPLCONFIGDIR=temporary,
                                   OPENBLAS_NUM_THREADS="1")
                script = (
                    "import json,sys; from stlmc.cli.installer import _probe_visualization; "
                    "print(json.dumps(_probe_visualization(sys.argv[1],sys.argv[2])))"
                )
                result = subprocess.run([sys.executable, "-c", script, module, packages[module]],
                                        env=environment, capture_output=True, text=True, timeout=30)
                if result.returncode:
                    status[module] = False, "probe exit {}: {}".format(result.returncode, result.stderr.strip())
                else:
                    available, detail = json.loads(result.stdout)
                    status[module] = bool(available), str(detail)
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            status[module] = False, str(error)
    return status


def _probe_visualization(module, spec):
    available, detail = solvers._python_package_status(module, module, spec, "version matches policy")
    if not available:
        return available, detail
    try:
        if module == "numpy":
            import numpy as np
            if float(np.dot([1, 2], [3, 4])) != 11:
                raise RuntimeError("dot product smoke failed")
        elif module == "scipy":
            from scipy.integrate import odeint
            values = odeint(lambda y, t: [1], [0], [0, 1])
            if abs(float(values[-1, 0]) - 1) > 1e-6:
                raise RuntimeError("ODE sampling smoke failed")
        elif module == "bokeh":
            from bokeh.plotting import figure
            from bokeh.embed import file_html
            from bokeh.resources import INLINE
            plot = figure()
            plot.line([0, 1], [0, 1])
            if "<html" not in file_html(plot, INLINE, "smoke").lower():
                raise RuntimeError("HTML smoke failed")
        elif module == "matplotlib":
            from io import BytesIO
            from matplotlib.figure import Figure
            from matplotlib.backends.backend_pdf import FigureCanvasPdf
            figure = Figure()
            figure.subplots().plot([0, 1], [0, 1])
            output = BytesIO()
            FigureCanvasPdf(figure).print_pdf(output)
            if not output.getvalue().startswith(b"%PDF-"):
                raise RuntimeError("PDF smoke failed")
        return True, detail + "; smoke check passed"
    except Exception as error:
        return False, detail + "; smoke check failed: " + str(error)


def _visualize(check=False, output_format="html"):
    package_specs = visualization_packages(sys.version_info)
    required = ["numpy", "scipy"] + {"html": ["bokeh"], "pdf": ["matplotlib"], "text": [],
                                      "all": ["bokeh", "matplotlib"]}[output_format]
    before = visualize_status(required)
    packages = {name: package_specs[name] for name in required}
    if not check:
        for module, package in packages.items():
            if not before[module][0]:
                solvers._install_python_package(package)
    status = visualize_status(required)
    for name in required:
        available, detail = status[name]
        print("{}: {} ({})".format(name, "available" if available else "unavailable", detail))
    return int(any(not status[name][0] for name in required))


def build_parser():
    parser = argparse.ArgumentParser(description="Install or check STLmc solver and visualization dependencies.")
    class UniqueSelection(argparse.Action):
        def __call__(self, parser, namespace, values, option_string=None):
            if getattr(namespace, self.dest, None) is not None or len(set(values)) != len(values):
                parser.error("{} must not be repeated or contain duplicate targets".format(option_string))
            setattr(namespace, self.dest, values)
    subparsers = parser.add_subparsers(dest="action")
    for action in ("install", "check"):
        command = subparsers.add_parser(action, help=("install explicitly selected dependencies" if action == "install" else "read-only version and capability checks"))
        command.add_argument("--solver", nargs="+", choices=["z3", "cvc5", "yices", "dreal"], action=UniqueSelection)
        command.add_argument("--visualize", nargs="+", choices=["html", "pdf", "text"], action=UniqueSelection)
        command.add_argument("--all", action="count", default=0, help="select all solvers and visualization formats")
        command.add_argument("--thread-safe", action="store_true", help="require native Yices thread safety")
        command.add_argument("--without-mcsat", action="store_true", help="Yices LRA/core-only; check accepts a full MCSAT installation too")
        if action == "install":
            builds = command.add_mutually_exclusive_group()
            builds.add_argument("--build", action="store_true", help="build Yices in a unique private user prefix")
            builds.add_argument("--experimental-build", action="store_true",
                                help="opt into the experimental dReal source build; ODE soundness is not certified")
            command.add_argument("--jobs", type=int, default=None, help="number of make build jobs (default: 1)")
            command.add_argument("--prefix", type=Path, help="managed user build root; system libraries are never replaced")
            command.add_argument("--source", type=Path, help="local Yices source tree; dReal builds use pinned sources")
    return parser


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.action is None:
        parser.print_help()
        return 0
    check = args.action == "check"
    if args.all > 1:
        parser.error("--all must not be repeated")
    if args.all and (args.solver or args.visualize):
        parser.error("--all cannot be combined with --solver or --visualize")
    if not check and not (args.all or args.solver or args.visualize):
        parser.error("install requires --solver, --visualize, or --all")
    select_all = args.all or (check and not args.solver and not args.visualize)
    selected_solvers = ["z3", "cvc5", "yices", "dreal"] if select_all else (args.solver or [])
    selected_visuals = ["html", "pdf", "text"] if select_all else (args.visualize or [])
    build = getattr(args, "build", False)
    experimental_build = getattr(args, "experimental_build", False)
    any_build = build or experimental_build
    jobs = getattr(args, "jobs", None)
    prefix, source = getattr(args, "prefix", None), getattr(args, "source", None)
    if jobs is not None and jobs < 1:
        parser.error("--jobs must be positive")
    if experimental_build and (selected_solvers != ["dreal"] or selected_visuals):
        parser.error("--experimental-build requires selecting only --solver dreal")
    if build and selected_solvers == ["dreal"]:
        parser.error("dReal source builds require explicit --experimental-build; --build is for Yices")
    if any_build or prefix is not None or source is not None or jobs is not None:
        if len(selected_solvers) != 1 or selected_solvers[0] not in {"yices", "dreal"} or selected_visuals:
            parser.error("source build options require selecting only --solver yices or only --solver dreal")
    if source is not None and selected_solvers == ["dreal"]:
        parser.error("--source is supported only for Yices; dReal builds use pinned sources")
    if not check and (args.thread_safe or args.without_mcsat or prefix is not None or source is not None or jobs is not None) and not any_build:
        parser.error("source build options require --build for Yices or --experimental-build for dReal")
    if (args.thread_safe or args.without_mcsat) and "yices" not in selected_solvers:
        parser.error("Yices capability options require --solver yices (or --all)")
    if check and args.without_mcsat and (selected_solvers != ["yices"] or selected_visuals):
        parser.error("--without-mcsat requires selecting only --solver yices")
    if not check and selected_visuals:
        try:
            # Reject an unsupported plan before installing any solver/package.
            visualization_packages(sys.version_info)
        except RuntimeError as error:
            print(str(error), file=sys.stderr)
            return 1
    failed = False
    for backend in selected_solvers:
        try:
            if any_build:
                if backend == "yices":
                    # Binding repair must succeed before activating a native build.
                    solvers._install_python_package(solvers._YICES_PACKAGE)
                    build_yices(prefix=prefix, source=source, thread_safe=args.thread_safe,
                                mcsat=not args.without_mcsat, jobs=jobs or 1)
                else:
                    print("Experimental dReal source build: passing feature probes does not certify general ODE soundness.", file=sys.stderr)
                    build_dreal(prefix=prefix, jobs=jobs or 1)
            else:
                backend_failed = bool(solvers.main([backend] + (["--check"] if check else [])))
                failed = backend_failed or failed
                if check and backend_failed:
                    # The baseline already explains a missing/wrong binding or
                    # library; capability probing cannot add useful information.
                    continue
            if check and backend == "yices":
                # Never initialize a native backend in this dispatcher process.
                script = """import sys
try:
 from stlmc.solver.availability import load_yices_binding
 y = load_yices_binding().Yices
 thread_safe = bool(y.is_thread_safe())
 mcsat = bool(y.has_mcsat())
except Exception as error:
 print('Yices unavailable: ' + ' '.join(str(error).split()), file=sys.stderr)
 raise SystemExit(1)
print('Yices capabilities: thread_safe={}, mcsat={}'.format(thread_safe, mcsat))
raise SystemExit(int((sys.argv[1] == '1' and not thread_safe) or (sys.argv[2] == '1' and not mcsat)))
"""
                environment = dict(os.environ)
                environment["PYTHONPATH"] = str(Path(__file__).resolve().parents[2]) + os.pathsep + environment.get("PYTHONPATH", "")
                result = subprocess.run([sys.executable, "-c", script, str(int(args.thread_safe)), str(int(not args.without_mcsat))],
                                        env=environment, capture_output=True, text=True, timeout=30)
                print(result.stdout, end="")
                if result.returncode:
                    print("Yices capability check failed (thread safety required={}, MCSAT required={}; probe exit {}): {}".format(
                        args.thread_safe, not args.without_mcsat, result.returncode, result.stderr.strip()), file=sys.stderr)
                    failed = True
        except (OSError, RuntimeError, subprocess.SubprocessError) as error:
            print(str(error), file=sys.stderr)
            failed = True
    for output_format in selected_visuals:
        try:
            failed = bool(_visualize(check=check, output_format=output_format)) or failed
        except (OSError, RuntimeError, subprocess.SubprocessError) as error:
            print(str(error), file=sys.stderr)
            failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
