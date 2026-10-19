"""Locations and discovery rules for external solver installations."""

import os
import shutil
import sys
import json
import hashlib
import re
import threading
from pathlib import Path
from urllib.parse import urlsplit

from ..exceptions import SolverUnavailableError


_yices_load_lock = threading.RLock()
_yices_dependency_handles = {}
_yices_managed_selection = None


def _selected_yices_installation():
    library = os.environ.get("STLMC_YICES_LIBRARY")
    origin = "STLMC_YICES_LIBRARY"
    dependencies = []
    if library is None:
        manifest = solver_data_dir() / "yices" / "active.json"
        if not manifest.exists():
            return None, ()
        origin = str(manifest)
        try:
            installation = json.loads(manifest.read_text())
            library = installation["library"]
            dependencies = installation.get("dependencies", [])
        except (OSError, ValueError, KeyError, TypeError) as error:
            raise SolverUnavailableError("invalid Yices installation manifest: {}".format(manifest)) from error
    if not isinstance(library, str) or not library or not Path(library).is_absolute():
        raise SolverUnavailableError("{} must select an absolute Yices library path".format(origin))
    if not Path(library).is_file():
        raise SolverUnavailableError(
            "Yices library selected by {} was not found: {}. Run: stlmc-installer install --solver yices".format(origin, library)
        )
    if not isinstance(dependencies, list):
        raise SolverUnavailableError("invalid Yices dependencies in {}".format(origin))
    verified = []
    for dependency in dependencies:
        try:
            path = dependency["library"]
            digest = dependency["sha256"]
            package_digest = dependency["package_sha256"]
            version = dependency["version"]
            source = urlsplit(dependency["source"])
            valid = (isinstance(path, str) and Path(path).is_absolute()
                     and isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest)
                     and isinstance(package_digest, str) and re.fullmatch(r"[0-9a-f]{64}", package_digest)
                     and isinstance(version, str) and bool(version.strip())
                     and source.scheme == "https" and bool(source.netloc))
            if not valid:
                raise ValueError("absolute library path, SHA256, version and HTTPS provenance are required")
            dependency_path = Path(path)
            if not dependency_path.is_file():
                raise ValueError("dependency library was not found: " + path)
            content_hash = hashlib.sha256()
            with dependency_path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    content_hash.update(chunk)
            if content_hash.hexdigest() != digest:
                raise ValueError("dependency SHA256 mismatch: " + path)
            verified.append((str(dependency_path.resolve()), digest))
        except (KeyError, TypeError, ValueError, AttributeError, OSError) as error:
            raise SolverUnavailableError(
                "invalid Yices dependency selected by {}: {}. Run: "
                "stlmc-installer install --solver yices".format(origin, error)) from error
    return str(Path(library).resolve()), tuple(verified)


def selected_yices_library():
    """Return an explicit/user-managed library, or None for system discovery.

    Explicit libraries never inherit dependencies from the managed manifest.
    """
    return _selected_yices_installation()[0]


def load_yices_binding():
    """Load the optional binding against the selected native library once.

    The upstream binding resolves its library during import. Restrict the
    discovery override to that import; never switch a live native library.
    """
    import ctypes.util
    from importlib import import_module
    global _yices_managed_selection

    with _yices_load_lock:
        library, dependencies = _selected_yices_installation()
        selection = (library, dependencies)
        loaded = sys.modules.get("yices")
        api = sys.modules.get("yices_api")
        if library is not None and (loaded is not None or api is not None):
            # Importing yices_api alone already opens libyices with CDLL.
            # Overriding find_library later cannot replace that cached native
            # handle when the high-level yices package is imported.
            native = getattr(api, "libyices", None)
            actual = getattr(native, "_name", None)
            if actual is None or str(Path(actual).resolve()) != library:
                raise SolverUnavailableError(
                    "a different Yices library is already loaded; restart the process to use {}".format(library)
                )
            if ((_yices_managed_selection is not None and _yices_managed_selection != selection)
                    or (dependencies and _yices_managed_selection is None)):
                raise SolverUnavailableError(
                    "Yices dependencies changed or were loaded outside STLmc; "
                    "restart the process to use the managed installation")
        if loaded is not None:
            return loaded
        if "cvc5" in sys.modules:
            raise SolverUnavailableError(
                "Yices must be initialized before the CVC5 extension; restart the process "
                "after configuring the Yices installation"
            )
        if library is None:
            return import_module("yices")
        if _yices_dependency_handles and set(_yices_dependency_handles) != set(dependencies):
            raise SolverUnavailableError(
                "different Yices dependencies are already loaded; "
                "restart the process to use the selected installation")
        for path, digest in dependencies:
            key = (path, digest)
            if key not in _yices_dependency_handles:
                try:
                    # Hold these handles for the process lifetime. A dependent
                    # SONAME can resolve without changing LD_LIBRARY_PATH.
                    _yices_dependency_handles[key] = ctypes.CDLL(path, mode=ctypes.RTLD_GLOBAL)
                except OSError as error:
                    raise SolverUnavailableError(
                        "could not load managed Yices dependency {}: {}. Run: "
                        "stlmc-installer install --solver yices".format(path, error)) from error
        original = ctypes.util.find_library
        ctypes.util.find_library = lambda name: library if name == "yices" else original(name)
        try:
            binding = import_module("yices")
            _yices_managed_selection = selection
            return binding
        finally:
            ctypes.util.find_library = original


def solver_data_dir():
    if sys.platform == "darwin":
        root = Path.home() / "Library" / "Application Support"
    else:
        root = Path(os.environ.get("XDG_DATA_HOME", Path.home() / ".local" / "share"))
    return root / "stlmc" / "solvers"


def user_dreal_path():
    return solver_data_dir() / "dReal3" / "dReal"


def find_dreal():
    # A validated managed installation must not be shadowed by an older PATH
    # executable. Explicit configuration paths bypass this default discovery.
    user_dreal = user_dreal_path()
    if user_dreal.is_file() and os.access(str(user_dreal), os.X_OK):
        return str(user_dreal)
    return shutil.which("dReal")
