"""Pinned dReal3 source builds isolated from existing solver installations.

Only the Linux/x86-64 GCC profile is implemented. Build tools and the OS/C++
SDK are prerequisites; solver libraries are built from content-pinned sources.
The caller owns activation of the returned executable.
"""

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import signal
import subprocess
import tarfile
import tempfile
import urllib.request
import venv

from .dependency_policy import DREAL_SOURCE_COMMIT, DREAL_SOURCE_SHA256, DREAL_SOURCE_URL


# Archive digests recorded from the exact upstream CMake dependency commits.
# These are content pins, not upstream signatures or independently certified
# binaries. No dependency is selected from an ambient solver-library prefix.
_DEPENDENCIES = (
    ("picosat", "8ea4bd467e9dcb3b37e212293f541a2be18f6406", "508cbe59520e9f2dcaa353fcf1047c71951e56f8a0567291ca38d36dc68f16c3"),
    ("filibxx", "d898fe000e157f44e4a84b8f79b4e7556a5d6fb5", "3044c46926a216ada7ec7d8613c882840ed7c482f66878bed70d751fc70f42d4"),
    ("glpk", "44ea53eed46d26e1c0ee815ee3e862ba181b1327", "e1b0a47da14e34881c63b688892446452669d99286846b65180447d9ecaad229"),
    ("nlopt", "dbf99e4bcea03c68063299ae77657a71151aa23a", "257aefe3b24b9f7fe552b6415ce55c8356e7eed864eea58916995d3969f72f79"),
    ("adept", "266ffc0282fcc49716915574647c06be9333e2dc", "5541a29151099d1a0d0e641925e1dccb17d63b6b678fdad49d7919a1c513c2ab"),
    ("capdDynSys-4.0", "f39f3942dd1bd4899821316efc0ca55483ab5071", "a23a19ea64fd43d0135445dd99b22afea8c61cc85db7222d125240af30aec1d3"),
    ("ibex-lib", "874d370fa23a0b56ec72565489e75149d4f2829e", "2f2cfaa95dd9e274f77ecb81113e778cbe92b52715c996d9ca88db5e3926fee6"),
    ("Catch", "5aa2b82b17aeeb935919b1d0bbb93bd0adc86ddb", "cfee3992ff3e245410f10f9589638fb4007325584e9fb9e3bee06f39245682bc"),
    ("easyloggingpp", "efcadc8649c959403dcdeeafbb24f958c05c866e", "3b09bbd608b07177980c0ba180319d773fd5fef47c8ee8e828d7c46ebd121dc8"),
    ("ezoptionparser", "2bdb6b0b75dfdc8614b05f0a1945b8b623bd040b", "f1126687e44bda779d2766b12b242c01f68514b848c3fb2b8cd51234a4cca396"),
    ("json", "9f9d293bad3792cb7120901b0d5ea7e93fc09b66", "1f4d0b9c057e965b351f136ac54053750c299412ea0b25f84acc28c66933cc37"),
)
_MAX_ARCHIVE = 64 * 1024 * 1024
_MAX_UNPACKED = 512 * 1024 * 1024
_CMAKE_VERSION = "3.29.6"
# Pull pthread_self into the static executable even when libstdc++ references
# it weakly. Upstream appends its full-static flags to this initial linker flag.
_STATIC_THREAD_LINK_FLAG = "-Wl,-u,pthread_self"


def _prepare_cmake(work, env, log):
    """Provision a disposable build tool, never modifying the caller's Python."""
    tool_env = work / "tool-env"
    venv.EnvBuilder(with_pip=True).create(str(tool_env))
    python = tool_env / "bin/python"
    _run([python, "-m", "pip", "--isolated", "--require-virtualenv",
          "--no-cache-dir", "install", "--index-url",
          "https://pypi.org/simple", "--only-binary=:all:", "--no-deps",
          "--disable-pip-version-check", "cmake==" + _CMAKE_VERSION], env, log,
         timeout=300)
    # Use the wheel's real executable, not its Python entry-point wrapper:
    # wrappers can select another interpreter through pyenv/PATH shims.
    candidates = list(tool_env.glob("lib/python*/site-packages/cmake/data/bin/cmake"))
    if len(candidates) != 1 or not candidates[0].is_file():
        raise RuntimeError("private CMake wheel did not provide its native executable")
    executable = candidates[0].resolve()
    if tool_env.resolve() not in executable.parents:
        raise RuntimeError("private CMake executable escapes its tool environment")
    version = subprocess.run([str(executable), "--version"], env=env,
                             capture_output=True, text=True, timeout=15, check=True)
    if version.stdout.splitlines()[:1] != ["cmake version " + _CMAKE_VERSION]:
        raise RuntimeError("private CMake version does not match " + _CMAKE_VERSION)
    return executable, {"version": _CMAKE_VERSION, "executable_sha256": _sha(executable),
                        "source": "PyPI binary wheel (version-pinned, not wheel-hash-pinned)"}


def _sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _download(url, digest, target, cache=None):
    """Fetch a content-pinned archive; optional cache never bypasses hashing."""
    if cache is not None and (cache / target.name).is_file():
        shutil.copyfile(str(cache / target.name), str(target))
    else:
        try:
            with urllib.request.urlopen(url, timeout=60) as response, target.open("wb") as stream:
                size = 0
                while True:
                    block = response.read(1024 * 1024)
                    if not block:
                        break
                    size += len(block)
                    if size > _MAX_ARCHIVE:
                        raise RuntimeError("dReal source archive exceeds size limit")
                    stream.write(block)
        except OSError as error:
            raise RuntimeError("Cannot download pinned dReal source {}: {}".format(url, error)) from error
    if target.stat().st_size > _MAX_ARCHIVE or _sha(target) != digest:
        raise RuntimeError("SHA256 mismatch for pinned source {}".format(target.name))
    return target


def _unpack(archive, destination):
    """Extract regular sources, materializing only safe internal symlinks."""
    destination.mkdir()
    with tarfile.open(str(archive), "r:gz") as tar:
        members = tar.getmembers()
        if len(members) > 100000 or sum(m.size for m in members) > _MAX_UNPACKED:
            raise RuntimeError("source archive exceeds unpacking limits")
        roots = set()
        names = {}
        links = []
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or not path.parts or ".." in path.parts or "\\" in member.name:
                raise RuntimeError("unsafe source archive path")
            roots.add(path.parts[0])
            if member.name in names:
                raise RuntimeError("duplicate source archive member")
            names[member.name] = member
            target = destination.joinpath(*path.parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(member) as incoming, target.open("wb") as stream:
                    shutil.copyfileobj(incoming, stream)
                target.chmod(0o755 if member.mode & 0o111 else 0o644)
                os.utime(str(target), (member.mtime, member.mtime))
            elif member.issym():
                links.append(member)
            else:
                raise RuntimeError("unsupported source archive member")
        if len(roots) != 1:
            raise RuntimeError("expected a single source archive root")
        for member in links:
            # Resolve text lexically before touching the filesystem. Real
            # symlinks are never created, so extraction cannot pivot outside.
            current = member
            seen = set()
            while current.issym():
                if current.name in seen or len(seen) > 16:
                    raise RuntimeError("cyclic source archive symlink")
                seen.add(current.name)
                if PurePosixPath(current.linkname).is_absolute() or "\\" in current.linkname:
                    raise RuntimeError("unsafe source archive symlink")
                import posixpath
                linked = posixpath.normpath(posixpath.join(posixpath.dirname(current.name), current.linkname))
                if linked not in names or PurePosixPath(linked).parts[0] not in roots:
                    raise RuntimeError("source archive symlink escapes its root")
                current = names[linked]
            if not current.isfile():
                raise RuntimeError("source archive symlink must reference a file")
            target = destination / member.name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(str(destination / current.name), str(target))
    return destination / roots.pop()


def _run(command, env, log, cwd=None, timeout=1800):
    with log.open("a", encoding="utf-8") as output:
        output.write("\nCOMMAND " + json.dumps([str(x) for x in command]) + "\n")
        output.flush()
        process = subprocess.Popen([str(x) for x in command], cwd=cwd, env=env,
                                   stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            raise
        if code:
            raise RuntimeError("dReal build command failed (exit {}); inspect {}".format(code, log))


def _prerequisites(jobs):
    if platform.system() != "Linux" or platform.machine().lower() not in ("x86_64", "amd64"):
        raise RuntimeError("dReal source build currently validates Linux x86-64 GCC only; this platform is unverified")
    if jobs is None:
        jobs = min(4, os.cpu_count() or 1)
    if isinstance(jobs, bool) or not isinstance(jobs, int) or jobs < 1:
        raise ValueError("dReal build jobs must be a positive integer")
    required = ("gcc", "g++", "make", "autoconf", "automake", "autoreconf", "libtoolize", "m4", "bison", "flex", "pkg-config", "git", "python2.7")
    tools = {name: shutil.which(name) for name in required}
    missing = [name for name, value in tools.items() if value is None]
    if missing:
        raise RuntimeError("Missing dReal build prerequisites: {}. Supply these build tools on PATH; no system packages were installed.".format(", ".join(missing)))
    return jobs, tools


def _patch_sources(source, build):
    changes = []
    def patch(path, description, transform):
        original = path.read_text()
        modified = transform(original)
        if modified == original:
            raise RuntimeError("Pinned dReal build patch did not apply: " + description)
        path.write_text(modified)
        changes.append({"file": str(path.relative_to(source)), "description": description,
                        "before_sha256": hashlib.sha256(original.encode()).hexdigest(),
                        "after_sha256": hashlib.sha256(modified.encode()).hexdigest()})
    # A source export below another checkout must not acquire its parent's
    # unrelated Git SHA. This is a provenance-only generated-metadata patch.
    patch(source / "src/util/CMakeLists.txt", "stamp exact source export commit, not ambient Git HEAD",
          lambda text: text.replace("get_git_head_revision(GIT_REFSPEC GIT_SHA1)",
                                    'set(GIT_SHA1 "{}")'.format(DREAL_SOURCE_COMMIT)))
    # Every third-party link must name the private static archive explicitly,
    # rather than falling back to a host library when a local file is absent.
    libraries = ("picosat", "prim", "glpk", "nlopt", "adept", "capd", "ibex")
    def static_links(text):
        for name in libraries:
            if 'set(EXTRA_LIBS "{}"'.format(name) not in text:
                raise RuntimeError("Pinned private library link was not found: " + name)
            text = text.replace('set(EXTRA_LIBS "{}"'.format(name),
                                'set(EXTRA_LIBS "${{CMAKE_CURRENT_BINARY_DIR}}/lib/lib{}.a"'.format(name))
        return text
    patch(source / "src/CMakeLists.txt", "link third-party libraries by explicit private static archive path", static_links)
    # Interpreter shims (notably pyenv's cmake shim) may rewrite PATH for
    # children. Never let waf's env-python shebang choose Python3 implicitly.
    patch(source / "src/CMakeLists.txt", "explicit Python2 for every IBEX waf configure/build/install command",
          lambda text: text.replace("${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf",
                                    "${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf"))
    return changes


def _audit_cache(build):
    values = {}
    cache = build / "CMakeCache.txt"
    for line in cache.read_text().splitlines():
        match = re.match(r"([^:#/][^:]*):[^=]+=(.*)$", line)
        if match:
            values[match.group(1)] = match.group(2)
    if _STATIC_THREAD_LINK_FLAG not in values.get("CMAKE_EXE_LINKER_FLAGS", "").split():
        raise RuntimeError("unsafe dReal static link: missing forced pthread_self definition")
    for key in ("USE_LOCAL_THIRD_PARTY", "SUPPORT_ODE", "BUILD_STATIC_BIN",
                "CMAKE_DISABLE_FIND_PACKAGE_GLPK", "CMAKE_DISABLE_FIND_PACKAGE_NLOPT", "CMAKE_DISABLE_FIND_PACKAGE_CLP"):
        if values.get(key, "").upper() not in ("TRUE", "ON", "1"):
            raise RuntimeError("unsafe dReal CMake configuration: " + key)
    for name in ("GLPK", "NLOPT", "CLP"):
        for key, value in values.items():
            if key.startswith(name + "_") and ("LIBRAR" in key or "INCLUDE" in key):
                if value and not value.endswith("-NOTFOUND"):
                    raise RuntimeError("ambient native dependency found in CMake cache: " + key)
    compilers = {}
    for language in ("C", "CXX"):
        files = list((build / "CMakeFiles").glob("*/CMake{}Compiler.cmake".format(language)))
        if len(files) != 1:
            raise RuntimeError("cannot establish the actual {} compiler identity".format(language))
        text = files[0].read_text()
        identity = re.search(r'set\(CMAKE_' + language + r'_COMPILER_ID "([^"]+)"\)', text)
        version = re.search(r'set\(CMAKE_' + language + r'_COMPILER_VERSION "([^"]+)"\)', text)
        if identity is None or identity.group(1) != "GNU" or version is None:
            raise RuntimeError("dReal interval arithmetic build requires verified GNU {} compiler identity/version".format(language))
        compilers[language] = {"id": identity.group(1), "version": version.group(1),
                               "cmake_metadata_sha256": _sha(files[0])}
    return {"sha256": _sha(cache), "compilers": compilers,
            "dependency_discovery": "GLPK/NLOPT/CLP disabled; local pinned sources only"}


def build_dreal(destination, jobs=None):
    """Build a pinned private prefix and return ``prefix/bin/dReal``.

    ``destination`` must not already exist. No existing installation is
    modified, and failed builds never publish a destination. Compiler/OS SDK
    libraries are prerequisites; native solver libraries are private builds.
    Successful builds retain source archives, applied source files, licenses,
    exact commands, hashes and linkage/runtime audit metadata.
    """
    destination = Path(destination).expanduser().absolute()
    if destination.exists() or destination.is_symlink():
        raise RuntimeError("dReal build destination already exists; choose a new private prefix")
    jobs, tools = _prerequisites(jobs)
    destination.parent.mkdir(parents=True, exist_ok=True)
    cache_raw = os.environ.get("STLMC_DREAL_SOURCE_CACHE")
    cache = Path(cache_raw).expanduser() if cache_raw else None
    with tempfile.TemporaryDirectory(prefix=".dreal-build-", dir=str(destination.parent)) as directory:
        work = Path(directory)
        prefix = work / "prefix"
        archives = prefix / "sources"
        archives.mkdir(parents=True)
        log = prefix / "build.log"
        inputs = [("dreal3", DREAL_SOURCE_COMMIT, DREAL_SOURCE_SHA256, DREAL_SOURCE_URL)]
        inputs += [(name, commit, digest, "https://codeload.github.com/dreal-deps/{}/tar.gz/{}".format(name, commit))
                   for name, commit, digest in _DEPENDENCIES]
        unpacked = {}
        records = []
        for name, commit, digest, url in inputs:
            archive = _download(url, digest, archives / (name + "-" + commit + ".tar.gz"), cache)
            unpacked[name] = _unpack(archive, work / ("source-" + name))
            records.append({"name": name, "commit": commit, "url": url, "sha256": digest})
        source = unpacked["dreal3"]
        build = work / "build"
        local = source / "src/third_party"
        local.mkdir()
        for name, _, _ in _DEPENDENCIES:
            dependency = unpacked[name]
            shutil.make_archive(str(local / name), "zip", root_dir=str(dependency.parent), base_dir=dependency.name)
        patches = _patch_sources(source, build)
        patch_files = prefix / "source-patches"
        patch_files.mkdir()
        for change in patches:
            target = patch_files / change["file"]
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(str(source / change["file"]), str(target))
        # Never inherit arbitrary host include/library prefixes, linker flags,
        # solver SDKs or make parallelism. PATH is used for explicit build-tool
        # prerequisites only; system compiler/OS runtime remains intentional.
        env = dict(os.environ)
        for key in ("LD_LIBRARY_PATH", "LD_PRELOAD", "DYLD_LIBRARY_PATH", "LIBRARY_PATH", "CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "CFLAGS", "CXXFLAGS", "CPPFLAGS", "LDFLAGS", "LIBS", "DESTDIR", "CMAKE_PREFIX_PATH", "CMAKE_LIBRARY_PATH", "CMAKE_INCLUDE_PATH", "CMAKE_FRAMEWORK_PATH", "CMAKE_TOOLCHAIN_FILE", "CMAKE_GENERATOR", "CMAKE_GENERATOR_INSTANCE", "CMAKE_GENERATOR_PLATFORM", "CMAKE_GENERATOR_TOOLSET", "CONFIG_SITE", "PKG_CONFIG_PATH", "PKG_CONFIG_SYSROOT_DIR", "PYTHONPATH", "PYTHONHOME", "MAKEFLAGS", "GNUMAKEFLAGS", "AM_MAKEFLAGS", "MFLAGS", "BASH_ENV", "ENV", "CC", "CXX", "AR", "RANLIB"):
            env.pop(key, None)
        env.update(LC_ALL="C", PKG_CONFIG_LIBDIR="", OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1")
        # Legacy IBEX waf invokes /usr/bin/env python, independently of the
        # CMake interpreter variable. Keep it on the required Python2 tool.
        tool_path = work / "build-tools"
        tool_path.mkdir()
        (tool_path / "python").symlink_to(tools["python2.7"])
        env["PATH"] = str(tool_path) + os.pathsep + env.get("PATH", os.defpath)
        env["PYTHONNOUSERSITE"] = "1"
        # A user-prefix libtool installation is not on aclocal's compiled-in
        # system search path. Keep its macros paired with that exact tool.
        libtool_macros = Path(tools["libtoolize"]).resolve().parent.parent / "share/aclocal"
        env["ACLOCAL_PATH"] = str(libtool_macros) if libtool_macros.is_dir() else ""
        env["LIBTOOLIZE"] = tools["libtoolize"]
        configure = ["cmake", "-G", "Unix Makefiles", "-S", source / "src", "-B", build,
            "-DCMAKE_EXE_LINKER_FLAGS=" + _STATIC_THREAD_LINK_FLAG,
            "-DCMAKE_BUILD_TYPE=Release", "-DCMAKE_C_COMPILER=" + tools["gcc"], "-DCMAKE_CXX_COMPILER=" + tools["g++"],
            "-DCMAKE_MAKE_PROGRAM=" + tools["make"], "-DBISON_EXECUTABLE=" + tools["bison"],
            "-DFLEX_EXECUTABLE=" + tools["flex"], "-DGIT_EXECUTABLE=" + tools["git"],
            "-DPKG_CONFIG_EXECUTABLE=" + tools["pkg-config"],
            "-DPYTHON_EXECUTABLE=" + tools["python2.7"], "-DSUPPORT_ODE=ON", "-DBUILD_TESTING=OFF",
            "-DBUILD_STATIC_BIN=ON", "-DBUILD_SHARED_LIBS=OFF", "-DUSE_LOCAL_THIRD_PARTY=ON",
            "-DCMAKE_DISABLE_FIND_PACKAGE_GLPK=TRUE", "-DCMAKE_DISABLE_FIND_PACKAGE_NLOPT=TRUE",
            "-DCMAKE_DISABLE_FIND_PACKAGE_CLP=TRUE", "-DCMAKE_FIND_USE_PACKAGE_REGISTRY=FALSE",
            "-DCMAKE_FIND_USE_SYSTEM_PACKAGE_REGISTRY=FALSE", "-DCMAKE_FIND_USE_CMAKE_ENVIRONMENT_PATH=FALSE",
            "-DCMAKE_FIND_USE_SYSTEM_ENVIRONMENT_PATH=FALSE"]
        try:
            cmake, cmake_tool = _prepare_cmake(work, env, log)
            tools["cmake"] = str(cmake)
            configure[0] = cmake
            _run(configure, env, log, timeout=120)
            cache_audit = _audit_cache(build)
            _run([tools["cmake"], "--build", build, "--target", "dReal-bin", "--parallel", str(jobs)], env, log)
            executable = prefix / "bin/dReal"
            executable.parent.mkdir()
            shutil.copy2(str(build / "dReal"), str(executable))
            from .native_linkage import audit_static_linkage
            from ..solver.dreal_runtime import validate_dreal_runtime
            linkage = audit_static_linkage(executable)
            runtime = validate_dreal_runtime(executable)
            runtime = dict(runtime, observed_staging_executable=str(executable),
                           executable=str(destination / "bin/dReal"))
            licenses = prefix / "licenses"
            licenses.mkdir()
            for name, tree in unpacked.items():
                for text in tree.rglob("*"):
                    if text.is_file() and text.name.upper().startswith(("LICENSE", "COPYING", "NOTICE", "AUTHORS")):
                        target = licenses / name / text.relative_to(tree)
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copyfile(str(text), str(target))
            manifest = {"source_commit": DREAL_SOURCE_COMMIT, "sources": records, "patches": patches,
                "platform": platform.platform(), "machine": platform.machine(), "jobs": jobs,
                "tools": tools, "cmake_tool": cmake_tool,
                "configure_command": [str(x) for x in configure],
                "build_environment": {key: env.get(key) for key in ("PATH", "ACLOCAL_PATH", "LIBTOOLIZE", "PKG_CONFIG_LIBDIR", "LC_ALL", "PYTHONNOUSERSITE")},
                "observed_build_directory": str(work), "published_prefix": str(destination),
                "policy": {"private_solver_dependencies": True, "clp": False, "ibex_lp": False,
                           "static_thread_link_flag": _STATIC_THREAD_LINK_FLAG,
                           "static_build_requested": True, "os_compiler_sdk": "host prerequisite"},
                "executable_sha256": _sha(executable), "linkage": linkage, "runtime": runtime}
            manifest["cmake_cache_audit"] = cache_audit
            (prefix / "build-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
            if destination.exists() or destination.is_symlink():
                raise RuntimeError("dReal destination appeared during build; existing prefix left untouched")
            prefix.rename(destination)
            return destination / "bin/dReal"
        except Exception as error:
            # Keep a compact diagnostic outside our temporary tree, without
            # preserving a partial installation or touching any other prefix.
            failure_log = destination.with_name(destination.name + ".failed-build.log")
            if log.exists() and not failure_log.exists():
                shutil.copyfile(str(log), str(failure_log))
            raise RuntimeError("dReal private build failed: {}. Diagnostic: {}. Existing installations were not changed.".format(error, failure_log)) from error
