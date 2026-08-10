import argparse
import os
import re
import shutil
import signal
import subprocess
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
BENCHMARK_ROOT = Path(__file__).resolve().parent / "benchmarks"
DREAL_EXECUTABLE = os.environ.get(
    "STLMC_DREAL",
    str(PROJECT_ROOT / "3rd_party" / "dReal3" / "dReal"),
)
ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
RESULT_PATTERN = re.compile(
    r"result\s*:\s*(True|False|Unknown)\s+(?:up to|at) bound\s+(\d+)"
)
EXPECTED_PATTERN = re.compile(
    r"^# @benchmark\.expected\((.+)\)$", re.MULTILINE
)
EXPECTED_ITEM_PATTERN = re.compile(r"(f\d+)=(True|False|Unknown):(\d+)")
FAST_PATTERN = re.compile(r"^# @benchmark\.fast\((.+)\)$", re.MULTILINE)
ACTIVE_PROCESSES = set()
ACTIVE_PROCESSES_LOCK = threading.Lock()
STOP_REQUESTED = threading.Event()


def discover_cases(scope):
    target = (BENCHMARK_ROOT / scope).resolve()
    benchmark_root = BENCHMARK_ROOT.resolve()
    if target != benchmark_root and benchmark_root not in target.parents:
        raise ValueError("scope must be inside the artifact benchmarks directory")
    if not target.exists():
        raise ValueError(f"artifact benchmark scope does not exist: {scope}")

    cases = []
    for model_path in sorted(target.rglob("*.model")):
        model_config = model_path.with_suffix(".cfg")
        specific_configs = sorted(model_path.parent.glob(f"{model_path.stem}-*.cfg"))
        for specific_config in specific_configs:
            cases.append((model_path, model_config, specific_config))
    return cases


def load_expected_result(case):
    model_path, _, specific_config = case
    label = specific_config.stem.rsplit("-", 1)[1]
    model_text = model_path.read_text(encoding="utf-8")
    annotation = EXPECTED_PATTERN.search(model_text)
    if annotation is None:
        return None
    expected = {
        item_label: (result, int(bound))
        for item_label, result, bound in EXPECTED_ITEM_PATTERN.findall(
            annotation.group(1)
        )
    }
    return expected.get(label)


def is_fast_case(case):
    model_path, _, specific_config = case
    label = specific_config.stem.rsplit("-", 1)[1]
    annotation = FAST_PATTERN.search(model_path.read_text(encoding="utf-8"))
    if annotation is None:
        return False
    fast_labels = {item.strip() for item in annotation.group(1).split(",")}
    return label in fast_labels


def terminate_process_group(process):
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            process.wait()
        except ChildProcessError:
            pass


def terminate_active_processes():
    with ACTIVE_PROCESSES_LOCK:
        processes = list(ACTIVE_PROCESSES)

    for process in processes:
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass

    deadline = time.monotonic() + 5
    for process in processes:
        if process.poll() is not None:
            continue
        try:
            process.wait(timeout=max(0, deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            pass

    for process in processes:
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
    for process in processes:
        try:
            process.wait()
        except ChildProcessError:
            pass


def run_case(executable, case, timeout, log_path):
    model_path, model_config, specific_config = case
    command = [
        executable,
        str(model_path),
        "-model-cfg", str(model_config),
        "-model-specific-cfg", str(specific_config),
        "-executable-path", DREAL_EXECUTABLE,
    ]
    started = time.monotonic()
    with ACTIVE_PROCESSES_LOCK:
        if STOP_REQUESTED.is_set():
            return "INTERRUPTED", None, 0.0, 130
        process = subprocess.Popen(
            command,
            cwd=PROJECT_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        ACTIVE_PROCESSES.add(process)
    timed_out = False
    try:
        try:
            output, _ = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            terminate_process_group(process)
            output, _ = process.communicate()
    finally:
        with ACTIVE_PROCESSES_LOCK:
            ACTIVE_PROCESSES.discard(process)

    elapsed = time.monotonic() - started
    output = ANSI_ESCAPE.sub("", output)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(output, encoding="utf-8")
    match = RESULT_PATTERN.search(output)
    result = "TIMEOUT" if timed_out else (match.group(1) if match else "ERROR")
    bound = int(match.group(2)) if match else None
    return result, bound, elapsed, process.returncode


def main():
    STOP_REQUESTED.clear()
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--scope", default=".",
        help="benchmark subtree, e.g. . or rail-poly",
    )
    parser.add_argument("--timeout", type=int, default=3600)
    parser.add_argument(
        "--fast", action="store_true",
        help="run only cases marked with @benchmark.fast",
    )
    parser.add_argument(
        "--jobs", type=int, default=1,
        help="number of benchmark cases to run concurrently",
    )
    parser.add_argument("--output", type=Path, default=Path("artifact-logs"))
    args = parser.parse_args()

    if args.jobs < 1:
        parser.error("--jobs must be at least 1")

    executable = os.environ.get("STLMC") or shutil.which("stlmc")
    if executable is None:
        raise SystemExit("stlmc executable was not found; install the package first")
    if not BENCHMARK_ROOT.is_dir():
        raise SystemExit(f"benchmark directory is missing: {BENCHMARK_ROOT}")

    cases = discover_cases(args.scope)
    if args.fast:
        cases = [case for case in cases if is_fast_case(case)]
    if not cases:
        raise SystemExit(f"no benchmark cases found under scope: {args.scope}")

    output_root = args.output
    failures = 0
    print(
        f"running {len(cases)} artifact benchmark cases from {args.scope} "
        f"with {args.jobs} job(s)"
    )

    jobs = []
    for case in cases:
        model_path, _, specific_config = case
        relative_model = model_path.relative_to(BENCHMARK_ROOT)
        case_name = f"{relative_model.parent.name}/{specific_config.stem}"
        log_path = output_root / relative_model.parent / f"{specific_config.stem}.log"
        jobs.append((case, case_name, log_path))

    executor = ThreadPoolExecutor(max_workers=args.jobs)
    futures = {}
    interrupted = False
    try:
        futures = {
            executor.submit(
                run_case, executable, case, args.timeout, log_path
            ): (case, case_name)
            for case, case_name, log_path in jobs
        }
        for index, future in enumerate(as_completed(futures), start=1):
            case, case_name = futures[future]
            try:
                result, bound, elapsed, returncode = future.result()
            except Exception as error:
                result, bound, elapsed, returncode = "ERROR", None, 0.0, 1
                print(f"{case_name}: runner error: {error}")

            expected = load_expected_result(case)
            passed = expected == (result, bound) and returncode == 0
            if not passed:
                failures += 1
            expected_text = (
                f"{expected[0]}@{expected[1]}" if expected is not None else "MISSING"
            )
            print(
                f"[{index:02d}/{len(cases):02d}] {case_name}: "
                f"{'PASS' if passed else 'FAIL'} "
                f"actual={result}@{bound} expected={expected_text} "
                f"({elapsed:.2f}s, exit={returncode})"
            )
    except KeyboardInterrupt:
        interrupted = True
        STOP_REQUESTED.set()
        for future in futures:
            future.cancel()
        print("\ninterrupted; terminating active benchmark processes...")
        terminate_active_processes()
    finally:
        executor.shutdown(wait=True)

    if interrupted:
        return 130

    if failures:
        raise SystemExit(f"{failures} of {len(cases)} benchmark cases failed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
