"""Local, single-user execution API. Run one Uvicorn worker on loopback."""
import json
import math
import os
import re
import signal
import subprocess
import sys
import threading
import time
import uuid
from contextlib import asynccontextmanager
from pathlib import Path
from typing import Literal

from fastapi import HTTPException
from pydantic import BaseModel, Field, field_validator

from . import documents
from .paths import data_dir

RUNS = Path(os.environ.get('STLMC_WEB_RUNS', str(data_dir() / 'runs'))).resolve()
LOCK = threading.RLock()
JOBS = {}
ACTIVE = None


def save_job(job):
    folder = RUNS / job['id']
    temporary = folder / 'job.tmp'
    temporary.write_text(json.dumps({k: v for k, v in job.items() if k != '_process'}), encoding='utf-8')
    temporary.replace(folder / 'job.json')


class RunRequest(BaseModel):
    model: str = Field(min_length=1, max_length=500_000)
    config: str = Field(default='', max_length=100_000)
    goal: str | None = Field(default=None, max_length=100, pattern=r'^[A-Za-z0-9_,]*$')
    solver: Literal['auto', 'z3', 'cvc5', 'yices', 'dreal'] | None = None
    bound: int | None = Field(default=None, ge=0, le=1000)
    time_bound: float | None = Field(default=None, gt=0, le=1000000)
    threshold: float | None = Field(default=None, ge=0, le=1000000)
    path_strategy: Literal['symbolic', 'explicit'] | None = None
    two_step: bool | None = None
    reach: bool | None = None
    timeout: int = Field(default=120, ge=1, le=3600)

    @field_validator('time_bound', 'threshold')
    @classmethod
    def finite(cls, value):
        if value is not None and not math.isfinite(value):
            raise ValueError('Must be finite')
        return value


def effective_config(request):
    """Pass only explicit browser changes to the shared config language."""
    from ..application.configuration import common_overrides_text
    values = {'goal': None if request.goal is None else request.goal or 'all',
              'bound': request.bound, 'time-bound': request.time_bound,
              'threshold': request.threshold, 'path-strategy': request.path_strategy,
              'two-step': request.two_step, 'reach': request.reach,
              'solver': request.solver}
    return request.config + common_overrides_text(values)


def stop_group(process):
    """Interrupt first, then kill the entire dedicated solver process group."""
    try:
        os.killpg(process.pid, signal.SIGINT)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    # A parent may have exited while a solver child is still alive.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def watch(job, process, stream):
    global ACTIVE
    try:
        process.wait(timeout=job['request']['timeout'])
        with LOCK:
            cancelled = job['state'] == 'stopping'
        if cancelled:
            stop_group(process)
        state = 'cancelled' if cancelled else ('completed' if process.returncode == 0 else 'failed')
    except subprocess.TimeoutExpired:
        stop_group(process)
        state = 'timed_out'
    finally:
        stream.close()
    with LOCK:
        job.update(state=state, finished=time.time(), exit_code=process.returncode)
        job.pop('_process', None)
        save_job(job)
        if ACTIVE == job['id']:
            ACTIVE = None


@asynccontextmanager
async def lifespan(app):
    yield
    with LOCK:
        active = JOBS.get(ACTIVE)
        process = active.get('_process') if active else None
        if active:
            active['state'] = 'stopping'
    if process:
        await __import__('asyncio').to_thread(stop_group, process)


def health():
    # Match the worker's interpreter and import path, rather than trusting
    # a top-level package name (which may be an old release or namespace).
    try:
        result = subprocess.run([sys.executable, '-m', 'stlmc.ui.worker',
                                 '--check-runtime'],
                                capture_output=True, text=True, timeout=15)
        return json.loads(result.stdout)
    except (OSError, subprocess.TimeoutExpired, json.JSONDecodeError) as error:
        return {'stlmc': False, 'python': sys.version.split()[0],
                'executable': sys.executable, 'location': None,
                'error': 'Could not check the STLMC runtime: {}'.format(error)}


def examples():
    result = []
    for item in documents.list_documents('model'):
        doc = documents.read_document(item['name'])
        stem = Path(doc['name']).stem
        result.append({'id': stem, 'name': stem.replace('-', ' ').title(),
                       'filename': doc['name'], 'model': doc['text'], 'revision': doc['revision']})
    return result



def load_job(run_id):
    if not re.fullmatch(r'[0-9a-f]{32}', run_id):
        raise HTTPException(404, 'Run not found')
    with LOCK:
        job = JOBS.get(run_id)
        if job:
            return {key: value for key, value in job.items() if key != '_process'}
    path = RUNS / run_id / 'job.json'
    if not path.is_file():
        raise HTTPException(404, 'Run not found')
    job = json.loads(path.read_text(encoding='utf-8'))
    if job['state'] in ('running', 'stopping'):
        job['state'] = 'interrupted'
    return job


def start(request: RunRequest):
    global ACTIVE
    if os.name != 'posix':
        raise HTTPException(503, 'This version requires Linux or macOS (or WSL).')
    runtime = health()
    if not runtime['stlmc']:
        raise HTTPException(503, runtime['error'])
    with LOCK:
        if ACTIVE:
            raise HTTPException(409, 'Another analysis is running. Stop it before starting a new one.')
        run_id = uuid.uuid4().hex
        folder = RUNS / run_id
        folder.mkdir(parents=True)
        (folder / 'input.model').write_text(request.model, encoding='utf-8')
        args = [sys.executable, '-u', '-m', 'stlmc.ui.worker', 'input.model', '-visualize']
        (folder / 'input.cfg').write_text(effective_config(request), encoding='utf-8')
        args += ['-model-cfg', 'input.cfg']
        snapshot = request.model_dump(exclude={'model', 'config'})
        job = dict(id=run_id, state='running', started=time.time(), finished=None,
                   exit_code=None, request=snapshot, command=['stlmc'] + args[4:])
        stream = (folder / 'run.log').open('wb')
        try:
            process = subprocess.Popen(args, cwd=folder, stdout=stream, stderr=subprocess.STDOUT,
                                       start_new_session=True, env={**os.environ, 'PYTHONUNBUFFERED': '1'})
        except OSError as error:
            stream.close()
            raise HTTPException(503, str(error))
        JOBS[run_id] = job
        job['owner_pid'] = os.getpid()
        ACTIVE = run_id
        save_job(job)
        job['_process'] = process
        threading.Thread(target=watch, args=(job, process, stream), daemon=True).start()
        return load_job(run_id)


def stop(run_id: str):
    load_job(run_id)
    with LOCK:
        job = JOBS.get(run_id)
        if job and job['state'] == 'running':
            job['state'] = 'stopping'
            threading.Thread(target=stop_group, args=(job['_process'],), daemon=True).start()
    return load_job(run_id)
