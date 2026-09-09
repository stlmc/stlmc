"""Termination and reaping policy for solver workers."""

import os
import signal
import subprocess
import threading
import time


def is_running(worker):
    if hasattr(worker, "poll"):
        return worker.poll() is None
    return worker.is_alive()


def _signal_process(worker, sig):
    try:
        if worker.process_group:
            os.killpg(worker.pid, sig)
        elif sig == signal.SIGTERM:
            worker.terminate()
        else:
            worker.kill()
    except ProcessLookupError:
        pass
    except PermissionError:
        # A process group may disappear or become inaccessible between poll
        # and killpg. The direct worker handle remains safe to signal.
        try:
            if sig == signal.SIGTERM:
                worker.terminate()
            else:
                worker.kill()
        except ProcessLookupError:
            pass


def _wait(worker, timeout):
    if hasattr(worker, "wait"):
        worker.wait(timeout=timeout)
    else:
        worker.join(timeout=timeout)


def terminate_workers(workers, timeout):
    """Stop workers using one shared graceful-shutdown deadline.

    Returns the workers that are known to be stopped and can be removed from
    the caller's registry.
    """
    workers = list(workers)
    thread_workers = [w for w in workers if w.worker_kind == "thread"]
    process_workers = [w for w in workers if w.worker_kind == "process"]

    for worker in thread_workers:
        worker.terminate()
    for worker in process_workers:
        if is_running(worker):
            _signal_process(worker, signal.SIGTERM)

    deadline = time.monotonic() + timeout
    for worker in process_workers:
        remaining = max(0.0, deadline - time.monotonic())
        if not is_running(worker):
            continue
        try:
            _wait(worker, remaining)
        except subprocess.TimeoutExpired:
            pass

    for worker in process_workers:
        if is_running(worker):
            _signal_process(worker, signal.SIGKILL)

    for worker in process_workers:
        try:
            _wait(worker, 1)
        except subprocess.TimeoutExpired:
            pass

    for worker in process_workers:
        completion_worker = getattr(worker, "completion_worker", None)
        if (
            completion_worker is not None
            and completion_worker is not threading.current_thread()
        ):
            completion_worker.join(timeout=1)

    return set(thread_workers).union(
        worker for worker in process_workers if not is_running(worker)
    )
