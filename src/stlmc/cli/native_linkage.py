"""Reject host third-party shared libraries in private native solver builds.

This is a linkage policy, not an execution sandbox or proof of numerical
correctness. System compiler/OS runtimes are permitted; solver dependencies
must be linked statically. Inspect files without running them (never ldd).
"""

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


_LINUX_RUNTIMES = frozenset({
    "libc.so.6", "libm.so.6", "libpthread.so.0", "libdl.so.2",
    "librt.so.1", "libutil.so.1", "libresolv.so.2",
    "libgcc_s.so.1", "libstdc++.so.6",
    "ld-linux-x86-64.so.2", "ld-linux-aarch64.so.1",
})


def _inspect(command):
    environment = dict(os.environ, LC_ALL="C")
    result = subprocess.run(command, capture_output=True, text=True,
                            timeout=30, check=True, env=environment)
    return result.stdout


def _tool(name):
    tool = shutil.which(name)
    if tool is None:
        raise RuntimeError("{} is required to audit native solver linkage".format(name))
    return tool


def _linux_linkage(executable):
    tool = _tool("readelf")
    header = _inspect([tool, "-h", str(executable)])
    if "ELF Header:" not in header or not re.search(r"(?m)^\s*Type:\s+(?:EXEC|DYN)\b", header):
        raise RuntimeError("Expected an ELF executable for Linux linkage audit")
    dynamic = _inspect([tool, "-d", str(executable)])
    program = _inspect([tool, "-l", str(executable)])
    if not re.search(r"(?m)^\s*LOAD\s", program):
        raise RuntimeError("Expected loadable ELF executable segments")
    no_dynamic = dynamic.strip() == "There is no dynamic section in this file."
    if no_dynamic:
        if re.search(r"(?m)^\s*DYNAMIC\s", program):
            raise RuntimeError("Inconsistent ELF dynamic section report")
        rows = []
    else:
        section = re.search(r"(?m)^Dynamic section at offset 0x[0-9a-fA-F]+ contains (\d+) entries:\s*$", dynamic)
        rows = re.findall(r"(?m)^\s*0x[0-9a-fA-F]+\s+\(([A-Z0-9_]+)\)\s+(.+?)\s*$", dynamic)
        if (section is None or len(rows) != int(section.group(1))
                or not rows or rows[-1][0] != "NULL"):
            raise RuntimeError("Unrecognized ELF dynamic section report")
        if any(tag in {"AUDIT", "DEPAUDIT", "FILTER", "AUXILIARY"} for tag, _ in rows):
            raise RuntimeError("Unexpected ELF auxiliary library loading directive")
    dependencies = re.findall(r"\(NEEDED\).*?\[([^\]]+)\]", dynamic)
    search_paths = re.findall(r"\((?:RPATH|RUNPATH)\).*?\[([^\]]*)\]", dynamic)
    interpreters = re.findall(r"Requesting program interpreter:\s*([^\]]+)\]", program)
    if (len(dependencies) != sum(tag == "NEEDED" for tag, _ in rows)
            or len(search_paths) != sum(tag in {"RPATH", "RUNPATH"} for tag, _ in rows)
            or len(interpreters) != len(re.findall(r"(?m)^\s*INTERP\s", program))):
        raise RuntimeError("Unrecognized ELF dependency or interpreter report")
    foreign = [dependency for dependency in dependencies
               if dependency not in _LINUX_RUNTIMES]
    # A native build must not carry a Homebrew/user-prefix loader override,
    # including $ORIGIN paths which could shadow the permitted OS runtimes.
    if search_paths:
        raise RuntimeError("Unexpected native loader search path: " + ", ".join(search_paths))
    for interpreter in interpreters:
        if (not interpreter.startswith(("/lib/", "/lib64/", "/usr/lib/", "/usr/lib64/"))
                or Path(interpreter).name not in _LINUX_RUNTIMES
                or ".." in Path(interpreter).parts):
            raise RuntimeError("Unexpected native interpreter: " + interpreter)
    if foreign:
        raise RuntimeError("Third-party shared libraries are not allowed: " + ", ".join(foreign))
    if dependencies and not interpreters:
        raise RuntimeError("Dynamic ELF file has no executable interpreter")
    return {"format": "ELF", "dependencies": dependencies,
            "interpreters": interpreters, "search_paths": search_paths,
            "fully_static": not dependencies and not interpreters}


def _macos_linkage(executable):
    tool = _tool("otool")
    output = _inspect([tool, "-L", str(executable)])
    # otool emits a heading per architecture for universal binaries. Require
    # all dependency lines to be understood rather than accepting partial data.
    dependencies = []
    headings = 0
    for line in output.splitlines():
        if not line.strip():
            continue
        if not line[0].isspace() and line.rstrip().endswith(":"):
            headings += 1
            continue
        match = re.fullmatch(r"\s+(.+?)\s+\(compatibility version [^)]*\)", line)
        if not match:
            raise RuntimeError("Unrecognized Mach-O dependency report: " + line)
        dependency = match.group(1)
        if (not dependency.startswith(("/usr/lib/", "/System/Library/"))
                or ".." in Path(dependency).parts):
            raise RuntimeError("Third-party shared libraries are not allowed: " + dependency)
        dependencies.append(dependency)
    if headings != 1 or not dependencies:
        raise RuntimeError("Expected a Mach-O executable with Apple system runtimes")
    loads = _inspect([tool, "-l", str(executable)])
    # Static dependency builds need no runtime search paths. Reject even an
    # otherwise unused entry so a private prefix cannot later be loaded.
    if re.search(r"(?m)^\s*cmd LC_RPATH\s*$", loads):
        raise RuntimeError("Unexpected Mach-O LC_RPATH in static-dependency build")
    if len(re.findall(r"(?m)^\s*cmd LC_MAIN\s*$", loads)) != 1:
        raise RuntimeError("Expected a Mach-O executable with LC_MAIN")
    if re.search(r"(?m)^\s*cmd LC_DYLD_ENVIRONMENT\s*$", loads):
        raise RuntimeError("Unexpected Mach-O loader environment override")
    loaders = re.findall(r"(?m)^\s*cmd LC_LOAD_DYLINKER\s*$", loads)
    system_loader = re.findall(
        r"(?m)^\s*cmd LC_LOAD_DYLINKER\s*\n\s*cmdsize \d+\s*\n\s*name /usr/lib/dyld \(offset \d+\)\s*$", loads)
    if len(loaders) != 1 or len(system_loader) != 1:
        raise RuntimeError("Expected the Apple system Mach-O interpreter /usr/lib/dyld")
    return {"format": "Mach-O", "dependencies": dependencies,
            "interpreters": ["/usr/lib/dyld"], "search_paths": [], "fully_static": False}


def audit_static_linkage(executable, *, platform=None):
    """Return JSON-safe evidence, or fail before a candidate is activated."""
    executable = Path(executable).resolve(strict=True)
    if not executable.is_file():
        raise RuntimeError("Native solver candidate is not a regular file")
    platform = sys.platform if platform is None else platform
    try:
        if platform.startswith("linux"):
            report = _linux_linkage(executable)
        elif platform == "darwin":
            report = _macos_linkage(executable)
        else:
            raise RuntimeError("Native linkage audit supports Linux and macOS only")
    except (OSError, subprocess.SubprocessError) as error:
        raise RuntimeError("Native linkage audit failed: {}".format(error)) from error
    report.update(executable=str(executable), policy="static-third-party-system-runtime-only")
    return report
