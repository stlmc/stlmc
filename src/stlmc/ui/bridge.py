"""Opt-in Pages-to-loopback API; never expose this service on a public interface."""
import argparse
import hmac
from importlib import metadata
import json
import math
import os
import stat
from contextlib import contextmanager
import re
import secrets
import sys
from urllib.parse import parse_qsl, urlsplit

from fastapi import FastAPI, HTTPException
from fastapi.exceptions import RequestValidationError
from lark import Lark, UnexpectedInput
from pydantic import ConfigDict, field_validator
from starlette.responses import JSONResponse, Response, StreamingResponse

from . import app as local

MAX_BODY = 1024 * 1024
FORBIDDEN_CONFIG = frozenset({'executable-path', 'save-smt2', 'smt2-dir'})
# Match STLmc config.lark syntax without importing STLmc: pairing/health must
# remain available before the runtime is installed. The worker still performs
# the authoritative configuration semantic validation, including inheritance.
_CONFIG = Lark(r'''
start: section*
section: NAME "extends" name_list "{" assignment* "}" | NAME "{" assignment* "}"
name_list: NAME ("," NAME)*
assignment: NAME "=" value?
?value: ESCAPED_STRING | SIGNED_NUMBER | NAME
NAME: /[a-zA-Z0-9_.\/-]+/
%import common.ESCAPED_STRING
%import common.SIGNED_NUMBER
%import common.WS
%ignore WS
%ignore /#[^\r\n]*/
%ignore /(?s:\'\'\'.*?\'\'\')/
''', parser='lalr')


def validate_config(text):
    """Inspect actual assignment keys, not comments or quoted values."""
    try:
        tree = _CONFIG.parse(text)
    except UnexpectedInput:
        raise ValueError('Invalid configuration syntax') from None
    if any(str(node.children[0]).lower() in FORBIDDEN_CONFIG
           for node in tree.find_data('assignment')):
        raise ValueError('Executable overrides and SMT file output are disabled in the bridge')
    return text


class BridgeRunRequest(local.RunRequest):
    model_config = ConfigDict(extra='forbid')

    @field_validator('config')
    @classmethod
    def safe_config(cls, value):
        return validate_config(value)


def canonical_origin(value):
    """Normalize configured origins only; incoming Origin must match exactly."""
    try:
        parsed = urlsplit(value)
        host = parsed.hostname
        port = parsed.port
        if (parsed.scheme not in {'http', 'https'} or not host or
                parsed.username is not None or parsed.password is not None or
                parsed.path not in {'', '/'} or parsed.query or parsed.fragment or
                not re.fullmatch(r'[A-Za-z0-9.:-]+', host) or
                (port is not None and not 1 <= port <= 65535)):
            raise ValueError()
        host = host.lower()
        if parsed.scheme == 'http' and host not in {'127.0.0.1', 'localhost', '::1'}:
            raise ValueError()
        host = '[' + host + ']' if ':' in host else host
        suffix = '' if port is None or (parsed.scheme, port) in {('http', 80), ('https', 443)} else ':' + str(port)
        return parsed.scheme + '://' + host + suffix
    except (TypeError, ValueError):
        raise ValueError('Use an exact HTTPS origin, or an HTTP loopback origin, without paths or wildcards') from None


class BridgeGuard:
    """Enforce authentication and bounded buffering before any endpoint runs."""
    def __init__(self, app, *, token, origins, port):
        self.app = app
        self._token = token
        self.origins = frozenset(origins)
        self.hosts = frozenset({'127.0.0.1:' + str(port), 'localhost:' + str(port)})

    async def __call__(self, scope, receive, send):
        if scope['type'] != 'http':
            if scope['type'] == 'websocket':
                await send({'type': 'websocket.close', 'code': 1008})
            else:
                await self.app(scope, receive, send)
            return
        headers = {}
        for key, value in scope.get('headers', []):
            headers.setdefault(key.lower(), []).append(value)
        def single(name):
            values = headers.get(name, [])
            if len(values) != 1:
                return None
            try:
                return values[0].decode('ascii')
            except UnicodeDecodeError:
                return None
        origin = single(b'origin')
        permitted = origin in self.origins
        cors = {'Access-Control-Allow-Origin': origin, 'Vary': 'Origin'} if permitted else {}
        async def fail(code, message, extra=None):
            response = JSONResponse({'detail': message}, status_code=code,
                                    headers={**cors, 'Cache-Control': 'no-store', **(extra or {})})
            await response(scope, receive, send)
        if single(b'host') is None or single(b'host').lower() not in self.hosts:
            await fail(403, 'Invalid bridge host')
            return
        if not permitted:
            await fail(403, 'Origin is not paired with this bridge')
            return
        if scope['method'] == 'OPTIONS':
            method = single(b'access-control-request-method')
            requested = single(b'access-control-request-headers')
            requested = {v.strip().lower() for v in requested.split(',')} if requested else set()
            if method not in {'GET', 'POST', 'PUT'} or not requested <= {'authorization', 'content-type'}:
                await fail(403, 'Preflight is not allowed')
                return
            result = {**cors, 'Access-Control-Allow-Methods': 'GET, POST, PUT',
                      'Access-Control-Allow-Headers': 'Authorization, Content-Type',
                      'Access-Control-Max-Age': '600', 'Cache-Control': 'no-store'}
            if single(b'access-control-request-private-network') == 'true':
                result['Access-Control-Allow-Private-Network'] = 'true'
            await Response(status_code=204, headers=result)(scope, receive, send)
            return
        authorization = single(b'authorization') or ''
        scheme, _, credential = authorization.partition(' ')
        if scheme.lower() != 'bearer' or not hmac.compare_digest(credential, self._token):
            await fail(401, 'A valid bridge session token is required', {'WWW-Authenticate': 'Bearer'})
            return
        query = parse_qsl(scope.get('query_string', b'').decode('ascii', errors='replace'))
        if any(key.lower().replace('-', '_') in {'token', 'access_token', 'session_token', 'authorization', 'bearer'}
               or self._token in value for key, value in query):
            await fail(400, 'Session tokens must not be supplied in URLs')
            return
        length = single(b'content-length')
        if b'content-length' in headers and (length is None or not length.isdecimal()):
            await fail(400, 'Invalid content length')
            return
        normalized = length.lstrip('0') or '0' if length is not None else '0'
        if len(normalized) > len(str(MAX_BODY)) or (len(normalized) == len(str(MAX_BODY)) and normalized > str(MAX_BODY)):
            await fail(413, 'Request body exceeds 1 MiB')
            return
        if b'transfer-encoding' in headers and length is not None:
            await fail(400, 'Ambiguous request framing')
            return
        body = bytearray()
        while True:
            message = await receive()
            if message['type'] == 'http.disconnect':
                return
            part = message.get('body', b'')
            if len(body) + len(part) > MAX_BODY:
                await fail(413, 'Request body exceeds 1 MiB')
                return
            body.extend(part)
            if not message.get('more_body', False):
                break
        replayed = False
        async def replay():
            nonlocal replayed
            if not replayed:
                replayed = True
                return {'type': 'http.request', 'body': bytes(body), 'more_body': False}
            return await receive()
        async def secured_send(message):
            if message['type'] == 'http.response.start':
                values = list(message.get('headers', []))
                values.extend([(b'access-control-allow-origin', origin.encode()), (b'vary', b'Origin'),
                               (b'cache-control', b'no-store'), (b'x-content-type-options', b'nosniff'),
                               (b'referrer-policy', b'no-referrer')])
                message = {**message, 'headers': values}
            await send(message)
        await self.app(scope, replay, secured_send)


@contextmanager
def _directory(path):
    """Open each directory component without following links, including ancestors."""
    descriptor = os.open('/', os.O_RDONLY | os.O_DIRECTORY)
    try:
        for component in path.absolute().parts[1:]:
            next_descriptor = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                      dir_fd=descriptor)
            os.close(descriptor)
            descriptor = next_descriptor
        yield descriptor
    except OSError:
        raise HTTPException(404, 'Run not found') from None
    finally:
        os.close(descriptor)


def _file(descriptor, name):
    try:
        fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=descriptor)
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            os.close(fd)
            raise HTTPException(404, 'File not found')
        return fd
    except FileNotFoundError:
        return None
    except OSError:
        raise HTTPException(404, 'File not found') from None


def _read(descriptor, name, *, tail=False):
    fd = _file(descriptor, name)
    if fd is None:
        return None
    with os.fdopen(fd, 'rb') as stream:
        if tail:
            stream.seek(max(0, os.fstat(stream.fileno()).st_size - 200_000))
        data = stream.read(2 * MAX_BODY + 1)
    if len(data) > 2 * MAX_BODY:
        raise HTTPException(413, 'Run metadata is too large')
    return data.decode('utf-8', errors='replace')


def _job(run_id, descriptor):
    with local.LOCK:
        memory = local.JOBS.get(run_id)
        if memory is not None:
            return {key: value for key, value in memory.items() if key != '_process'}
    try:
        job = json.loads(_read(descriptor, 'job.json') or 'null')
        if (not isinstance(job, dict) or job.get('id') != run_id or
                not isinstance(job.get('started'), (float, int)) or not math.isfinite(job['started'])):
            raise ValueError()
    except (ValueError, TypeError):
        raise HTTPException(404, 'Run not found') from None
    if job.get('state') in {'running', 'stopping'}:
        job['state'] = 'interrupted'
    return job


def _records(descriptor, name):
    records = []
    for line in (_read(descriptor, name) or '').splitlines():
        try:
            item = json.loads(line)
            if isinstance(item, dict):
                records.append(item)
        except ValueError:
            pass  # The worker may still be writing its last line.
    return records


def create_app(*, token, allow_origins, port=8765):
    if not isinstance(token, str) or len(token) < 32 or not token.isascii():
        raise ValueError('Use a fresh, high-entropy session token')
    if not 1 <= port <= 65535:
        raise ValueError('Invalid bridge port')
    origins = {canonical_origin(v) for v in allow_origins}
    if not origins:
        raise ValueError('At least one paired origin is required')
    app = FastAPI(title='STLmc local bridge', lifespan=local.lifespan,
                  docs_url=None, redoc_url=None, openapi_url=None)
    app.add_middleware(BridgeGuard, token=token, origins=origins, port=port)
    @app.exception_handler(RequestValidationError)
    async def invalid_request(request, exception):
        # Python's JSON parser accepts NaN/Infinity. Pydantic correctly rejects
        # them, but the default error contains the original non-finite input
        # and ValueError context, neither of which is strict-JSON serializable.
        def safe(value):
            if isinstance(value, float) and not math.isfinite(value):
                return str(value)
            if isinstance(value, dict):
                return {str(key): safe(item) for key, item in value.items()}
            if isinstance(value, (tuple, list)):
                return [safe(item) for item in value]
            if value is None or isinstance(value, (str, bool, int, float)):
                return value
            return str(value)
        return JSONResponse({'detail': safe(exception.errors())}, status_code=422)
    runs = local.RUNS

    @contextmanager
    def run_directory(run_id):
        if not re.fullmatch('[0-9a-f]{32}', run_id):
            raise HTTPException(404, 'Run not found')
        with _directory(runs / run_id) as descriptor:
            yield descriptor

    @app.get('/api/runs')
    def history():
        if not runs.exists():
            return []
        jobs = []
        with _directory(runs) as descriptor:
            names = os.listdir(descriptor)
        for name in names:
            try:
                with run_directory(name) as descriptor:
                    jobs.append(_job(name, descriptor))
            except HTTPException:
                continue
        return sorted(jobs, key=lambda item: item['started'], reverse=True)[:100]

    @app.get('/api/runs/{run_id}')
    def detail(run_id: str):
        with run_directory(run_id) as descriptor:
            job = _job(run_id, descriptor)
            job['log'] = _read(descriptor, 'run.log', tail=True) or ''
            job['results'] = _records(descriptor, 'results.jsonl')
            rendering = _records(descriptor, 'visualization.jsonl')
            job['visualization_errors'] = [item['error'] for item in rendering if item.get('error')]
            job['progress'] = {'events': _records(descriptor, 'progress.jsonl'), 'scenario': None}
            scenario = _read(descriptor, 'scenario.json')
            if scenario:
                try:
                    job['progress']['scenario'] = json.loads(scenario)
                except ValueError:
                    pass
            files = []
            for name in os.listdir(descriptor):
                try:
                    info = os.stat(name, dir_fd=descriptor, follow_symlinks=False)
                except FileNotFoundError:
                    continue  # A worker may atomically replace metadata while listing.
                if (stat.S_ISREG(info.st_mode) and info.st_nlink == 1 and
                        name.rsplit('.', 1)[-1] in {'model', 'cfg', 'counterexample', 'witness', 'html', 'log'}):
                    files.append(name)
            job['files'] = sorted(files)
            return job

    @app.get('/api/runs/{run_id}/files/{name}')
    def download(run_id: str, name: str, inline: bool = False):
        if not re.fullmatch(r'[A-Za-z0-9_.-]{1,240}', name) or name not in detail(run_id)['files']:
            raise HTTPException(404, 'File not found')
        with run_directory(run_id) as descriptor:
            fd = _file(descriptor, name)
        if fd is None:
            raise HTTPException(404, 'File not found')
        def chunks():
            with os.fdopen(fd, 'rb') as stream:
                while chunk := stream.read(64 * 1024):
                    yield chunk
        headers = {}
        media_type = 'application/octet-stream'
        if inline and name.endswith('.html'):
            media_type = 'text/html'
            headers['Content-Security-Policy'] = "sandbox allow-scripts; default-src 'none'; script-src 'unsafe-inline' 'unsafe-eval' https://cdn.bokeh.org; style-src 'unsafe-inline'; img-src data: blob:; font-src data:; worker-src blob:"
        else:
            headers['Content-Disposition'] = 'attachment; filename="' + name + '"'
        return StreamingResponse(chunks(), media_type=media_type, headers=headers)

    @app.post('/api/runs/{run_id}/stop')
    def stop(run_id: str):
        with run_directory(run_id) as descriptor:
            job = _job(run_id, descriptor)
        with local.LOCK:
            active = run_id in local.JOBS
        return local.stop(run_id) if active else job
    @app.get('/api/bridge')
    def bridge_info():
        try:
            version = metadata.version('stlmc')
        except metadata.PackageNotFoundError:
            version = None
        return {'protocol': 1, 'version': version,
                'capabilities': ['health', 'examples', 'documents', 'runs', 'stop', 'artifacts']}
    for path, endpoint in [('/api/health', local.health), ('/api/examples', local.examples),
                           ('/api/documents', local.documents.list_documents),
                           ('/api/documents/{name}', local.documents.get_document)]:
        app.add_api_route(path, endpoint, methods=['GET'])
    @app.put('/api/documents/{name}')
    def save_document(name: str, request: local.documents.SaveRequest):
        if name.endswith('.cfg'):
            try:
                validate_config(request.text)
            except ValueError as error:
                raise HTTPException(422, str(error)) from None
        return local.documents.save_document(name, request)
    @app.post('/api/runs', status_code=201)
    def start(request: BridgeRunRequest):
        # The local worker creates a fresh unpredictable child; reject a replaced
        # or symlinked configured root before delegating that creation.
        if runs.exists() or runs.is_symlink():
            with _directory(runs):
                pass
        return local.start(request)
    return app


def show_pairing(token, origins, port, workspace_url=None):
    """Never send credentials to redirected stdout/stderr or the logging system."""
    paired = list(origins)
    text = 'Bridge API (not a web page): http://127.0.0.1:{}\n'.format(port)
    if workspace_url is not None:
        text = 'Local workspace: {}\n'.format(workspace_url) + text
        parsed = urlsplit(workspace_url)
        local_origins = {'{}://{}:{}'.format(parsed.scheme, host, parsed.port)
                         for host in ('127.0.0.1', 'localhost')}
        paired = [origin for origin in paired if origin not in local_origins]
    if paired:
        text += 'Paired website origin(s): {}\n'.format(', '.join(paired))
    text += 'Session token (paste only into your trusted STLmc page): {}\n'.format(token)
    text += 'Keep this terminal open; paste the session token into the workspace to connect.\n'
    for stream in (sys.stderr, sys.stdout):
        if stream.isatty():
            stream.write(text)
            stream.flush()
            return
    try:
        with open('/dev/tty', 'w', encoding='utf-8') as terminal:
            terminal.write(text)
    except OSError:
        raise RuntimeError('Start the bridge in an interactive terminal to display its session token securely') from None


def main(argv=None):
    parser = argparse.ArgumentParser(description='Pair a trusted web page with a single-user, loopback-only STLmc bridge.')
    parser.add_argument('--allow-origin', action='append', required=True, help='Exact trusted HTTPS origin; repeat to pair another origin')
    parser.add_argument('--port', type=int, default=8765)
    args = parser.parse_args(argv)
    try:
        origins = sorted({canonical_origin(v) for v in args.allow_origin})
        token = secrets.token_urlsafe(32)
        app = create_app(token=token, allow_origins=origins, port=args.port)
        show_pairing(token, origins, args.port)
    except (ValueError, RuntimeError) as error:
        parser.error(str(error))
    import uvicorn
    uvicorn.run(app, host='127.0.0.1', port=args.port, workers=1,
                access_log=False, proxy_headers=False, server_header=False, ws='none')
