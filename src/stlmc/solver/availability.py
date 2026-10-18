"""Locations and discovery rules for external solver installations."""

import os
import shutil
import sys
import json
import threading
from pathlib import Path

from ..exceptions import SolverUnavailableError


_yices_load_lock = threading.RLock()


def selected_yices_library():
    """Return an explicit/user-managed library, or None for system discovery."""
    library = os.environ.get("STLMC_YICES_LIBRARY")
    origin = "STLMC_YICES_LIBRARY"
    if library is None:
        manifest = solver_data_dir() / "yices" / "active.json"
        if not manifest.exists():
            return None
        origin = str(manifest)
        try:
            library = json.loads(manifest.read_text())["library"]
        except (OSError, ValueError, KeyError, TypeError) as error:
            raise SolverUnavailableError("invalid Yices installation manifest: {}".format(manifest)) from error
    if not isinstance(library, str) or not library or not Path(library).is_absolute():
        raise SolverUnavailableError("{} must select an absolute Yices library path".format(origin))
    if not Path(library).is_file():
        raise SolverUnavailableError(
            "Yices library selected by {} was not found: {}. Run: stlmc-installer install --solver yices".format(origin, library)
        )
    return str(Path(library).resolve())


def load_yices_binding():
    """Load the optional binding against the selected native library once.

    The upstream binding resolves its library during import. Restrict the
    discovery override to that import; never switch a live native library.
    """
    import ctypes.util
    from importlib import import_module

    with _yices_load_lock:
        library = selected_yices_library()
        loaded = sys.modules.get("yices")
        if loaded is not None:
            native = getattr(sys.modules.get("yices_api"), "libyices", None)
            actual = getattr(native, "_name", None)
            if library is not None and (actual is None or str(Path(actual).resolve()) != library):
                raise SolverUnavailableError(
                    "a different Yices library is already loaded; restart the process to use {}".format(library)
                )
            return loaded
        if "cvc5" in sys.modules:
            raise SolverUnavailableError(
                "Yices must be initialized before the CVC5 extension; restart the process "
                "after configuring the Yices installation"
            )
        if library is None:
            return import_module("yices")
        original = ctypes.util.find_library
        ctypes.util.find_library = lambda name: library if name == "yices" else original(name)
        try:
            return import_module("yices")
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
