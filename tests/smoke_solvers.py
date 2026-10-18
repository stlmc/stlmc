import argparse
import hashlib
import os
import re
import shlex
import shutil
import subprocess
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
TEST_ROOT = Path(__file__).resolve().parent / "smt2"

# This exception observes a specific upstream defect, not a correct result.
# Changing any of these inputs requires an explicit policy review.
KNOWN_DREAL_CASE = "zero-derivative-parameter-unsat.smt2"
KNOWN_DREAL_HASHES = (
    "abc9a1cdc1d931c1a43914dcd1748809724e35178c0157c32ed11c98bbc6a42e",
    "f49de52b54aa9e7ef99bbdff9b67da3fa538d71e5375bf765cb5722d050c9784",
    "5c17dfcc2a8f1f30d9e96df6a9825a5030ade046d560332c19de74d93d591a18",
)
KNOWN_DREAL_OUTPUT = "delta-sat with delta = 0.00000100000000000\n"


def known_dreal_fixture(input_path):
    paths = (input_path, input_path.with_suffix(input_path.suffix + ".args"),
             input_path.with_suffix(input_path.suffix + ".expected"))
    try:
        hashes = tuple(hashlib.sha256(path.read_bytes()).hexdigest() for path in paths)
    except OSError as error:
        raise RuntimeError("Cannot verify known-defect fixture fingerprint") from error
    if hashes != KNOWN_DREAL_HASHES:
        raise RuntimeError("Known-defect fixture fingerprint changed; review the smoke policy")


def official_dreal_version(executable):
    result = subprocess.run([executable, "--version"], stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, timeout=5)
    if result.returncode != 0 or result.stderr:
        raise RuntimeError("dReal version probe failed; no known-defect exception applies")
    return re.fullmatch(r"dReal v3\.16\.06\.02 \(commit [0-9a-fA-F]+\)",
                        result.stdout.strip()) is not None


def find_executable(name, configured_path=None):
    executable = configured_path or shutil.which(name)
    if executable is None or not Path(executable).is_file():
        raise RuntimeError(f"{name} executable was not found")
    return executable


def run_solver(name, executable, test_directory, *, allow_known_dreal_bugs=False):
    counts = {"PASS": 0, "XFAIL": 0, "XPASS": 0}
    official_version = None
    for input_path in sorted(test_directory.glob("*.smt2")):
        expected_path = input_path.with_suffix(input_path.suffix + ".expected")
        expected = expected_path.read_text(encoding="utf-8")
        known_case = (allow_known_dreal_bugs and name == "dReal"
                      and input_path.name == KNOWN_DREAL_CASE)
        if known_case:
            known_dreal_fixture(input_path)
            if official_version is None:
                official_version = official_dreal_version(executable)
        arguments_path = input_path.with_suffix(input_path.suffix + ".args")
        arguments = (
            shlex.split(arguments_path.read_text(encoding="utf-8"))
            if arguments_path.is_file() else []
        )
        result = subprocess.run(
            [executable, *arguments, str(input_path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            raise RuntimeError(
                f"{name} failed for {input_path.name}: {result.stderr.strip()}"
            )
        if known_case and result.stderr:
            raise RuntimeError("dReal emitted unexpected diagnostics; no known-defect exception applies: "
                               + result.stderr.strip())
        if result.stdout != expected:
            if known_case and official_version and result.stdout == KNOWN_DREAL_OUTPUT:
                counts["XFAIL"] += 1
                print(f"[XFAIL] {name}: {input_path.name} (known upstream invariant defect; not a correctness pass)")
                continue
            raise AssertionError(
                f"{name} output mismatch for {input_path.name}\n"
                f"expected: {expected!r}\nactual: {result.stdout!r}"
            )
        outcome = "XPASS" if known_case and official_version else "PASS"
        counts[outcome] += 1
        print(f"[{outcome}] {name}: {input_path.name}")
    return counts


def main(argv=None):
    parser = argparse.ArgumentParser(description="Strict solver smoke checks; known defects require explicit opt-in.")
    parser.add_argument("--allow-known-dreal-bugs", action="store_true",
                        help="observe the pinned official dReal invariant defect as XFAIL, not a correctness pass")
    args = parser.parse_args(argv)
    dreal_path = os.environ.get(
        "STLMC_DREAL",
        str(PROJECT_ROOT / "3rd_party" / "dReal3" / "dReal"),
    )
    solvers = [
        ("Yices", find_executable("yices-smt2"), TEST_ROOT / "yices2"),
        ("Z3", find_executable("z3"), TEST_ROOT / "z3"),
        ("dReal", find_executable("dReal", dreal_path), TEST_ROOT / "dreal"),
    ]
    totals = {"PASS": 0, "XFAIL": 0, "XPASS": 0}
    for name, executable, test_directory in solvers:
        counts = run_solver(name, executable, test_directory,
                            allow_known_dreal_bugs=args.allow_known_dreal_bugs)
        for outcome in totals:
            totals[outcome] += counts[outcome]
    print("Smoke summary: {PASS} PASS, {XPASS} XPASS, {XFAIL} known-defect XFAIL."
          .format(**totals))
    return totals


if __name__ == "__main__":
    main()
