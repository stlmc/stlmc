"""Utilities for optionally retaining solver input as SMT2 files."""

import re
from pathlib import Path


def is_enabled(config):
    common = config.get_section("common")
    return (
        common.is_argument_in("save-smt2")
        and common.get_value("save-smt2") == "true"
    )


def write_smt2(config, solver_name, debug_name, content):
    common = config.get_section("common")
    output_root = Path(
        common.get_value("smt2-dir")
        if common.is_argument_in("smt2-dir")
        else "smt2-logs"
    )
    safe_name = re.sub(r"[^A-Za-z0-9_.-]+", "_", debug_name or "query")
    output_dir = output_root / solver_name
    output_dir.mkdir(parents=True, exist_ok=True)

    # The algorithm supplies a meaningful query name (bound/scenario). Use
    # exclusive creation so concurrent workers and independent STLMC runs can
    # never overwrite one another. A suffix is needed only when a prior run
    # already produced the same semantic query name.
    collision_index = 1
    while True:
        suffix = "" if collision_index == 1 else "_{}".format(collision_index)
        output_path = output_dir / "{}{}.smt2".format(safe_name, suffix)
        try:
            with output_path.open("x", encoding="utf-8") as output_file:
                output_file.write(content)
            return str(output_path)
        except FileExistsError:
            collision_index += 1
