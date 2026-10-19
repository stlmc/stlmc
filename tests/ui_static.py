"""The unauthenticated page server exposes a fixed, no-follow asset set."""
import functools
import json
from http.client import HTTPConnection
from http.server import ThreadingHTTPServer
from pathlib import Path
import tempfile
import threading
import unittest

from stlmc.ui.static_server import ASSETS, StaticAssetHandler


class UiStaticAssetTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.static = self.root / 'static'; self.static.mkdir()
        for relative, _ in ASSETS.values():
            target = self.static / relative
            target.parent.mkdir(exist_ok=True)
            target.write_bytes(b'public asset')
        self.secret = self.root / 'secret'; self.secret.write_bytes(b'private secret')
        self.server = ThreadingHTTPServer(('127.0.0.1', 0),
            functools.partial(StaticAssetHandler, directory=self.static, bridge_port=18080))
        thread = threading.Thread(target=self.server.serve_forever,
                                  kwargs={'poll_interval': .01}, daemon=True)
        thread.start()
        def cleanup():
            self.server.shutdown(); self.server.server_close(); thread.join(timeout=5)
        self.addCleanup(cleanup)

    def request(self, target, method='GET'):
        connection = HTTPConnection('127.0.0.1', self.server.server_port, timeout=5)
        try:
            connection.request(method, target)
            response = connection.getresponse()
            return response.status, response.read(), dict(response.getheaders())
        finally:
            connection.close()

    def test_exact_assets_and_head(self):
        for path in ASSETS:
            with self.subTest(path=path):
                self.assertEqual(self.request(path)[:2], (200, b'public asset'))
        status, body, headers = self.request('/app.js', 'HEAD')
        self.assertEqual((status, body), (200, b''))
        self.assertEqual(headers['X-Content-Type-Options'], 'nosniff')

    def test_local_connection_contains_only_configured_address(self):
        status, body, headers = self.request('/local-connection.json')
        self.assertEqual(status, 200)
        self.assertEqual(json.loads(body), {'bridge_url': 'http://127.0.0.1:18080'})
        self.assertEqual(headers['Cache-Control'], 'no-store')
        self.assertNotIn('Access-Control-Allow-Origin', headers)
        self.assertEqual(self.request('/local-connection.json', 'HEAD')[:2], (200, b''))

    def test_listing_traversal_unlisted_and_write_methods_denied(self):
        for path in ['/examples/', '/../secret', '/%2e%2e/secret', '/secret', '/worker.py']:
            with self.subTest(path=path):
                status, body, _ = self.request(path)
                self.assertEqual(status, 404)
                self.assertNotIn(b'private secret', body)
        self.assertEqual(self.request('/app.js', 'POST')[0], 501)

    def test_symlinked_allowed_filename_denied(self):
        target = self.static / 'app.js'; target.unlink(); target.symlink_to(self.secret)
        self.assertEqual(self.request('/app.js')[0], 404)

    def test_symlinked_asset_directory_denied(self):
        import shutil
        shutil.rmtree(self.static / 'examples')
        (self.static / 'examples').symlink_to(self.root, target_is_directory=True)
        (self.root / 'therm-tutorial.model').write_bytes(b'private secret')
        self.assertEqual(self.request('/examples/therm-tutorial.model')[0], 404)

    def test_hard_linked_allowed_filename_denied(self):
        import os
        target = self.static / 'app.js'; target.unlink(); os.link(self.secret, target)
        self.assertEqual(self.request('/app.js')[0], 404)

    def test_nonregular_asset_denied_without_blocking(self):
        import os
        target = self.static / 'app.js'; target.unlink(); os.mkfifo(target)
        self.assertEqual(self.request('/app.js')[0], 404)


if __name__ == '__main__':
    unittest.main()
