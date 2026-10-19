"""Serve only bundled UI assets, never arbitrary package or user files."""
from http.server import BaseHTTPRequestHandler
import json
import os
import shutil
import stat
from urllib.parse import urlsplit


ASSETS = {
    '/': ('index.html', 'text/html; charset=utf-8'),
    '/index.html': ('index.html', 'text/html; charset=utf-8'),
    '/app.js': ('app.js', 'text/javascript; charset=utf-8'),
    '/styles.css': ('styles.css', 'text/css; charset=utf-8'),
    **{'/js/' + name + '.js': ('js/' + name + '.js', 'text/javascript; charset=utf-8')
       for name in ('connection', 'documents', 'analysis', 'results', 'progress', 'view')},
    '/examples/therm-tutorial.model': ('examples/therm-tutorial.model', 'text/plain; charset=utf-8'),
    '/examples/therm-tutorial.cfg': ('examples/therm-tutorial.cfg', 'text/plain; charset=utf-8'),
}


class StaticAssetHandler(BaseHTTPRequestHandler):
    def __init__(self, *args, directory, bridge_port=None, **kwargs):
        self.directory = str(directory)
        self.bridge_port = bridge_port
        super().__init__(*args, **kwargs)

    def log_message(self, format, *values):
        pass

    def _serve(self, head=False):
        if self.path == '/local-connection.json' and self.bridge_port is not None:
            body = json.dumps({'bridge_url': 'http://127.0.0.1:' + str(self.bridge_port)}).encode('utf-8')
            self.send_response(200)
            self.send_header('Content-Type', 'application/json; charset=utf-8')
            self.send_header('Content-Length', str(len(body)))
            self.send_header('Cache-Control', 'no-store')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.end_headers()
            if not head:
                self.wfile.write(body)
            return
        try:
            asset = ASSETS.get(urlsplit(self.path).path)
        except ValueError:
            asset = None
        if asset is None:
            self.send_error(404)
            return
        relative, content_type = asset
        descriptor = None
        try:
            # All path components come from the fixed manifest, not the URL.
            # Anchor each open to the previous directory and reject symlinks
            # at both the directory and file boundaries, including races.
            descriptor = os.open(self.directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            components = relative.split('/')
            for component in components[:-1]:
                child = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                dir_fd=descriptor)
                os.close(descriptor)
                descriptor = child
            file_descriptor = os.open(components[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                                      dir_fd=descriptor)
            with os.fdopen(file_descriptor, 'rb') as stream:
                info = os.fstat(stream.fileno())
                if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                    raise OSError('Static assets must be single-link regular files')
                self.send_response(200)
                self.send_header('Content-Type', content_type)
                self.send_header('Content-Length', str(info.st_size))
                self.send_header('X-Content-Type-Options', 'nosniff')
                self.send_header('Cache-Control', 'no-store')
                self.end_headers()
                if not head:
                    shutil.copyfileobj(stream, self.wfile)
        except OSError:
            self.send_error(404)
        finally:
            if descriptor is not None:
                os.close(descriptor)

    def do_GET(self):
        self._serve()

    def do_HEAD(self):
        self._serve(head=True)
