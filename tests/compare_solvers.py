import argparse
import os
import re
import signal
import shutil
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import run_artifact_benchmarks as benchmarks


PROJECT_ROOT = Path(__file__).resolve().parent.parent
SOLVER_PATTERN = re.compile(r'\bsolver\s*=\s*"([^"]+)"')
LOGIC_PATTERN = re.compile(
    r'\byices\s*\{.*?\blogic\s*=\s*"([^"]+)".*?\}', re.DOTALL
)
Z3_SLOW_PATTERN = re.compile(
    r"^# @benchmark\.z3-slow\((.+)\)$", re.MULTILINE
)


def model_uses_yices(case):
    _, model_config, _ = case
    match = SOLVER_PATTERN.search(model_config.read_text(encoding="utf-8"))
    return match is not None and match.group(1) == "yices"


def yices_logic(case):
    _, model_config, _ = case
    match = LOGIC_PATTERN.search(model_config.read_text(encoding="utf-8"))
    if match is None:
        raise ValueError("cannot find Yices logic in {}".format(model_config))
    return match.group(1)


def is_z3_slow_case(case):
    model_path, _, specific_config = case
    label = specific_config.stem.rsplit("-", 1)[1]
    annotation = Z3_SLOW_PATTERN.search(
        model_path.read_text(encoding="utf-8")
    )
    if annotation is None:
        return False
    labels = {item.strip() for item in annotation.group(1).split(",")}
    return label in labels


def case_paths(case, output_root):
    model_path, _, specific_config = case
    relative_model = model_path.relative_to(benchmarks.BENCHMARK_ROOT)
    output_dir = output_root / relative_model.parent
    return (
        output_dir / "{}.log".format(specific_config.stem),
        output_dir / "{}.z3.log".format(specific_config.stem),
    )


def read_result(output):
    match = benchmarks.RESULT_PATTERN.search(
        benchmarks.ANSI_ESCAPE.sub("", output)
    )
    if match is None:
        return None
    return match.group(1), int(match.group(2))


def run_z3(executable, case, timeout, log_path):
    model_path, model_config, specific_config = case
    command = [
        executable,
        str(model_path),
        "-model-cfg", str(model_config),
        "-model-specific-cfg", str(specific_config),
        "-solver", "z3",
        "-logic", yices_logic(case),
    ]
    started = time.monotonic()
    with benchmarks.ACTIVE_PROCESSES_LOCK:
        if benchmarks.STOP_REQUESTED.is_set():
            return None, 0.0, 130
        process = subprocess.Popen(
            command,
            cwd=PROJECT_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        benchmarks.ACTIVE_PROCESSES.add(process)
    try:
        try:
            output, _ = process.communicate(timeout=timeout)
            returncode = process.returncode
            parsed = read_result(output)
        except subprocess.TimeoutExpired:
            benchmarks.terminate_process_group(process)
            output, _ = process.communicate()
            returncode = 124
            parsed = None
    finally:
        with benchmarks.ACTIVE_PROCESSES_LOCK:
            benchmarks.ACTIVE_PROCESSES.discard(process)
    output = benchmarks.ANSI_ESCAPE.sub("", output)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(output, encoding="utf-8")
    return parsed, time.monotonic() - started, returncode


def main():
    benchmarks.STOP_REQUESTED.clear()
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", default=".")
    parser.add_argument("--timeout", type=int, default=3600)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--fast", action="store_true")
    parser.add_argument("--output", type=Path, default=Path("artifact-logs"))
    args = parser.parse_args()

    executable = os.environ.get("STLMC") or shutil.which("stlmc")
    if executable is None:
        raise SystemExit("stlmc executable was not found; install the package first")
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")

    cases = [
        case for case in benchmarks.discover_cases(args.scope)
        if model_uses_yices(case)
    ]
    if args.fast:
        cases = [
            case for case in cases
            if benchmarks.is_fast_case(case) and not is_z3_slow_case(case)
        ]
    if not cases:
        raise SystemExit("no Yices benchmark cases found under {}".format(args.scope))

    print(
        "comparing Z3 with Yices for {} benchmark cases with {} job(s)".format(
            len(cases), args.jobs
        )
    )
    failures = 0
    interrupted = False
    executor = ThreadPoolExecutor(max_workers=args.jobs)
    futures = {}
    try:
        for case in cases:
            yices_log, z3_log = case_paths(case, args.output)
            if not yices_log.exists():
                raise SystemExit(
                    "Yices benchmark log is missing: {}; run benchmark first".format(
                        yices_log
                    )
                )
            yices_result = read_result(yices_log.read_text(encoding="utf-8"))
            future = executor.submit(
                run_z3, executable, case, args.timeout, z3_log
            )
            futures[future] = (case, yices_result)

        for index, future in enumerate(as_completed(futures), start=1):
            case, yices_result = futures[future]
            model_path, _, specific_config = case
            name = "{}/{}".format(model_path.parent.name, specific_config.stem)
            z3_result, elapsed, returncode = future.result()
            passed = (
                yices_result is not None
                and z3_result == yices_result
                and returncode == 0
            )
            if passed:
                outcome = "PASS"
            else:
                failures += 1
                outcome = "FAIL"
            print(
                "[{}/{}] {}: {} yices={} z3={} ({:.2f}s, exit={})".format(
                    str(index).zfill(2),
                    str(len(cases)).zfill(2),
                    name,
                    outcome,
                    yices_result,
                    z3_result,
                    elapsed,
                    returncode,
                )
            )
    except KeyboardInterrupt:
        interrupted = True
        benchmarks.STOP_REQUESTED.set()
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        print("\ninterrupted; terminating active Z3 processes...", flush=True)
        for future in futures:
            future.cancel()
        benchmarks.terminate_active_processes()
    finally:
        executor.shutdown(wait=True)

    if interrupted:
        return 130
    if failures:
        raise SystemExit(
            "{} of {} Z3/Yices comparisons failed".format(failures, len(cases))
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
