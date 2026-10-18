"""Dependency-free version and source revision display for command-line tools."""

from importlib.metadata import PackageNotFoundError, version
from pathlib import Path
import re
import subprocess


TITLE = "STLmc - Signal Temporal Logic Model Checker"


def package_version():
    try:
        return version("stlmc")
    except PackageNotFoundError:
        return "development"


def _source_commit(root):
    """Inspect this source tree, never an unrelated repository in the cwd."""
    root = Path(root).resolve()
    if not (root / ".git").exists():
        return None

    def git(*arguments):
        return subprocess.run(
            ["git", "-C", str(root), *arguments], capture_output=True,
            text=True, check=True, timeout=1,
        ).stdout.strip()

    try:
        if Path(git("rev-parse", "--show-toplevel")).resolve() != root:
            return None
        commit = git("rev-parse", "HEAD")
        if re.fullmatch(r"[0-9a-fA-F]{40,64}", commit) is None:
            return None
        dirty = git("status", "--porcelain", "--untracked-files=normal", "--",
                    "src/stlmc", "pyproject.toml", "setup.py")
        return commit[:12].lower() + ("-dirty" if dirty else "")
    except (OSError, subprocess.SubprocessError, ValueError):
        return None


def source_commit():
    root = Path(__file__).resolve().parents[2]
    if (root / "src" / "stlmc" / "version_info.py").resolve() == Path(__file__).resolve():
        commit = _source_commit(root)
        if commit:
            return commit
    try:
        from ._build_info import COMMIT
    except ImportError:
        return "unknown"
    if isinstance(COMMIT, str) and re.fullmatch(r"[0-9a-f]{12,64}(?:-dirty)?", COMMIT):
        return COMMIT[:12] + ("-dirty" if COMMIT.endswith("-dirty") else "")
    return "unknown"


def version_line():
    return "v{} (commit: {})".format(package_version(), source_commit())


def banner():
    return "{}\n{}".format(TITLE, version_line())
