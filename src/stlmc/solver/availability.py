"""Locations and discovery rules for external solver installations."""

import os
import shutil
import sys
from pathlib import Path


def solver_data_dir():
    if sys.platform == "darwin":
        root = Path.home() / "Library" / "Application Support"
    else:
        root = Path(os.environ.get("XDG_DATA_HOME", Path.home() / ".local" / "share"))
    return root / "stlmc" / "solvers"


def user_dreal_path():
    return solver_data_dir() / "dReal3" / "dReal"


def find_dreal():
    path_dreal = shutil.which("dReal")
    if path_dreal:
        return path_dreal
    user_dreal = user_dreal_path()
    if user_dreal.is_file() and os.access(str(user_dreal), os.X_OK):
        return str(user_dreal)
    return None
