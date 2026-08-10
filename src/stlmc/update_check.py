"""Best-effort notification when a newer STLmc release is available."""

import json
import os
import re
import sys
import time
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path
from urllib.request import Request, urlopen


_PYPI_URL = "https://pypi.org/pypi/stlmc/json"
_CACHE_MAX_AGE = 24 * 60 * 60


def _cache_path():
    if sys.platform == "darwin":
        root = Path.home() / "Library" / "Caches"
    else:
        root = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    return root / "stlmc" / "update-check.json"


def _version_key(value):
    """Return a comparison key for the PEP 440 versions used by STLmc."""
    match = re.fullmatch(r"(\d+(?:\.\d+)*)(?:(a|b|rc|\.dev)(\d+))?", value)
    if match is None:
        return None
    release = tuple(int(part) for part in match.group(1).split("."))
    phase = match.group(2)
    phase_order = {".dev": 0, "a": 1, "b": 2, "rc": 3, None: 4}
    return release, phase_order[phase], int(match.group(3) or 0)


def _newer(latest, current):
    latest_key = _version_key(latest)
    current_key = _version_key(current)
    return latest_key is not None and current_key is not None and latest_key > current_key


def _read_cached_latest(now):
    try:
        data = json.loads(_cache_path().read_text(encoding="utf-8"))
        if now - float(data["checked_at"]) < _CACHE_MAX_AGE:
            return True, data.get("latest")
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return False, None


def _fetch_latest():
    request = Request(_PYPI_URL, headers={"User-Agent": "stlmc-update-check"})
    with urlopen(request, timeout=0.5) as response:
        return json.load(response)["info"]["version"]


def _write_cache(now, latest):
    try:
        path = _cache_path()
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps({"checked_at": now, "latest": latest}), encoding="utf-8"
        )
    except OSError:
        pass


def notify_if_outdated():
    """Print an update notice without ever preventing STLmc from running."""
    if os.environ.get("STLMC_DISABLE_UPDATE_CHECK", "").lower() in {"1", "true", "yes"}:
        return

    try:
        current = version("stlmc")
    except PackageNotFoundError:
        return

    now = time.time()
    cache_is_fresh, latest = _read_cached_latest(now)
    if not cache_is_fresh:
        try:
            latest = _fetch_latest()
        except (OSError, ValueError, KeyError, TypeError):
            _write_cache(now, None)
            return
        _write_cache(now, latest)

    if latest and _newer(latest, current):
        print(
            "A newer STLmc version is available: {} (installed: {}). "
            "Upgrade with: python -m pip install --upgrade stlmc".format(latest, current),
            file=sys.stderr,
        )
