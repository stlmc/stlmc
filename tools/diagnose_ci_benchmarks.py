"""Run unchanged timeout candidates serially and retain diagnostic evidence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CASES = (('bouncing-ball-ode', 'ball', 'f3', 3),
         ('bouncing-ball-ode', 'ball', 'f4', 2),
         ('tank-bounded-ode', 'tank', 'f1', 1))
RESULT = re.compile(r'status\s*:\s*(violated|satisfied|unknown)(?: at| up to)? bound (\d+)')


def file_info(path):
    path = Path(path)
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return {'path': str(path), 'size': path.stat().st_size, 'sha256': digest.hexdigest()}


def parse_processes(text):
    rows = []
    for line in text.splitlines():
        fields = line.strip().split(None, 4)
        if len(fields) != 5:
            continue
        try:
            rows.append({'pid': int(fields[0]), 'ppid': int(fields[1]),
                         'pcpu': float(fields[2]), 'rss_kib': int(fields[3]),
                         'comm': fields[4]})
        except ValueError:
            continue
    return rows


def process_tree(rows, parent):
    selected = {parent}
    while True:
        expanded = selected | {row['pid'] for row in rows if row['ppid'] in selected}
        if expanded == selected:
            return [row for row in rows if row['pid'] in selected]
        selected = expanded


def snapshot(pid):
    result = subprocess.run(['ps', '-axo', 'pid=,ppid=,%cpu=,rss=,comm='],
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=5)
    if result.returncode:
        raise RuntimeError('ps failed: ' + result.stderr.strip())
    return process_tree(parse_processes(result.stdout), pid)


def stop_process(process):
    if process.poll() is not None:
        return
    try:
        # STLmc handles SIGINT by cleaning up its separately grouped workers.
        os.killpg(process.pid, signal.SIGINT)
        process.wait(timeout=10)
    except ProcessLookupError:
        pass
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait(timeout=5)


def cpu_summary(before, after, elapsed):
    user = after.ru_utime - before.ru_utime
    system = after.ru_stime - before.ru_stime
    return {'user_seconds': user, 'system_seconds': system,
            'average_cpu_percent_one_core': 100 * (user + system) / elapsed if elapsed else 0,
            'scope': 'RUSAGE_CHILDREN: reaped descendants; includes diagnostic ps processes'}


def run_case(case, output, executable, dreal, timeout):
    directory, basename, goal, expected_bound = case
    working = output / (directory + '-' + goal)
    working.mkdir(parents=True, exist_ok=False)
    model_dir = ROOT / 'tests/benchmarks' / directory
    inputs = [model_dir / (basename + suffix) for suffix in
              ('.model', '.cfg', '-' + goal + '.cfg')]
    command = [executable, str(inputs[0]), '-model-cfg', str(inputs[1]),
               '-model-specific-cfg', str(inputs[2]), '-executable-path', dreal,
               '-visualize', '-parallel-core', '1', '-save-smt2',
               '-smt2-dir', str(working / 'smt2')]
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    timed_out = False
    samples = []
    with (working / 'stdout.log').open('w') as log:
        process = subprocess.Popen(command, cwd=working, stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while process.poll() is None:
                elapsed = time.monotonic() - started
                if elapsed >= timeout:
                    timed_out = True
                    stop_process(process)
                    break
                try:
                    samples.append({'elapsed_seconds': elapsed,
                                    'stdout_bytes': (working / 'stdout.log').stat().st_size,
                                    'processes': snapshot(process.pid)})
                except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
                    samples.append({'elapsed_seconds': elapsed, 'error': str(error)})
                try:
                    process.wait(timeout=min(2, max(.01, timeout - (time.monotonic() - started))))
                except subprocess.TimeoutExpired:
                    pass
        finally:
            stop_process(process)
    elapsed = time.monotonic() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    text = (working / 'stdout.log').read_text(errors='replace')
    match = RESULT.search(text)
    status, bound = (match[1], int(match[2])) if match else (None, None)
    result = {'case': directory + '/' + goal, 'command': command,
              'inputs': [file_info(path) for path in inputs],
              'timeout_seconds': timeout, 'elapsed_including_cleanup_seconds': elapsed,
              'timed_out': timed_out, 'returncode': process.returncode,
              'status': status, 'bound': bound, 'expected_status': 'violated',
              'expected_bound': expected_bound,
              'match': not timed_out and process.returncode == 0 and
                       status == 'violated' and bound == expected_bound,
              'cpu': cpu_summary(before, after, elapsed),
              'smt2': [file_info(path) for path in sorted(working.rglob('*.smt2'))]}
    (working / 'processes.json').write_text(json.dumps(samples, indent=2) + '\n')
    (working / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT / '.tmp/ci-timeout-diagnostics')
    parser.add_argument('--timeout', type=int, default=200)
    args = parser.parse_args()
    if args.timeout < 1:
        parser.error('--timeout must be positive')
    from stlmc.solver.availability import find_dreal
    import shutil
    dreal, executable = find_dreal(), shutil.which('stlmc')
    if not dreal or not executable:
        parser.error('installed stlmc and dReal are required')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    version = subprocess.run([dreal, '--version'], text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=15)
    metadata = {'python': sys.version, 'executable': sys.executable,
                'platform': platform.platform(), 'machine': platform.machine(),
                'cpu_count': os.cpu_count(), 'dreal': file_info(dreal),
                'dreal_version': version.stdout, 'dreal_version_returncode': version.returncode}
    import importlib.metadata
    metadata['stlmc_version'] = importlib.metadata.version('stlmc')
    revision = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
    metadata['checkout_commit'] = revision.stdout.strip() if revision.returncode == 0 else None
    metadata['measurement_notes'] = [
        'One case and one final solver worker at a time; original model/configuration files.',
        'SMT2 export and process sampling add diagnostic I/O/CPU overhead.',
        '200-second limit covers the entire CLI; elapsed additionally includes cleanup.',
        'Process CPU percentages are ps-reported values, not exact phase timings.']
    (output / 'environment.json').write_text(json.dumps(metadata, indent=2) + '\n')
    results = []
    for case in CASES:
        try:
            result = run_case(case, output, executable, dreal, args.timeout)
        except Exception as error:
            result = {'case': case[0] + '/' + case[2], 'match': False, 'error': str(error)}
        results.append(result)
        (output / 'summary.json').write_text(json.dumps(results, indent=2) + '\n')
        print('{}: match={} timeout={} elapsed={}'.format(result['case'], result['match'],
              result.get('timed_out'), result.get('elapsed_including_cleanup_seconds')), flush=True)
    return 0 if all(result['match'] for result in results) else 1


if __name__ == '__main__':
    raise SystemExit(main())
