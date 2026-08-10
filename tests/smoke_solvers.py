import os
import shutil
import subprocess
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
TEST_ROOT = Path(__file__).resolve().parent / "smt2"


def find_executable(name, configured_path=None):
    executable = configured_path or shutil.which(name)
    if executable is None or not Path(executable).is_file():
        raise RuntimeError(f"{name} executable was not found")
    return executable


def run_solver(name, executable, test_directory):
    for input_path in sorted(test_directory.glob("*.smt2")):
        expected_path = input_path.with_suffix(input_path.suffix + ".expected")
        expected = expected_path.read_text(encoding="utf-8")
        result = subprocess.run(
            [executable, str(input_path)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=30,
        )
        if result.returncode != 0:
            raise RuntimeError(
                f"{name} failed for {input_path.name}: {result.stderr.strip()}"
            )
        if result.stdout != expected:
            raise AssertionError(
                f"{name} output mismatch for {input_path.name}\n"
                f"expected: {expected!r}\nactual: {result.stdout!r}"
            )
        print(f"[PASS] {name}: {input_path.name}")


def main():
    dreal_path = os.environ.get(
        "STLMC_DREAL",
        str(PROJECT_ROOT / "3rd_party" / "dReal3" / "dReal"),
    )
    solvers = [
        ("Yices", find_executable("yices-smt2"), TEST_ROOT / "yices2"),
        ("Z3", find_executable("z3"), TEST_ROOT / "z3"),
        ("dReal", find_executable("dReal", dreal_path), TEST_ROOT / "dreal"),
    ]
    for name, executable, test_directory in solvers:
        run_solver(name, executable, test_directory)


if __name__ == "__main__":
    main()
