"""Launch the optional browser workspace without importing UI for CLI help."""
import argparse
import os
from pathlib import Path
import secrets
import sys


def main(argv=None):
    parser = argparse.ArgumentParser(prog='stlmc-gui',
        description='Run a local browser workspace and authenticated solver bridge.')
    parser.add_argument('--port', type=int, default=8765, help='Loopback API port (default: 8765)')
    parser.add_argument('--ui-port', type=int, default=8766, help='Loopback static page port (default: 8766)')
    parser.add_argument('--allow-origin', action='append', default=[],
                        help='Also pair an exact trusted HTTPS Pages origin; repeat as needed')
    parser.add_argument('--no-browser', action='store_true', help='Do not automatically open the local page')
    args = parser.parse_args(argv)
    if os.name != 'posix':
        parser.error('The local UI worker requires Linux, macOS, or WSL')
    if not all(1 <= value <= 65535 for value in (args.port, args.ui_port)) or args.port == args.ui_port:
        parser.error('API and UI ports must be distinct integers between 1 and 65535')
    try:
        import uvicorn
        from ..ui.bridge import canonical_origin, create_app, show_pairing
        from ..ui import documents
        from ..ui.paths import seed_examples
    except ImportError as error:
        print('UI dependencies are unavailable ({}). Run: stlmc-installer install --ui'.format(error),
              file=sys.stderr)
        return 2
    try:
        origins = sorted({canonical_origin(value) for value in args.allow_origin} |
                         {'http://127.0.0.1:' + str(args.ui_port),
                          'http://localhost:' + str(args.ui_port)})
    except ValueError as error:
        parser.error(str(error))
    import functools
    from http.server import ThreadingHTTPServer
    from ..ui.static_server import StaticAssetHandler
    import threading
    import webbrowser
    static = Path(__file__).resolve().parents[1] / 'ui' / 'static'

    try:
        server = ThreadingHTTPServer(('127.0.0.1', args.ui_port),
                                    functools.partial(StaticAssetHandler, directory=str(static)))
    except OSError as error:
        print('Cannot start the local page: {}'.format(error), file=sys.stderr)
        return 2
    try:
        seed_examples(documents.DIRECTORY)
        token = secrets.token_urlsafe(32)
        app = create_app(token=token, allow_origins=origins, port=args.port)
        url = 'http://127.0.0.1:' + str(args.ui_port) + '/'
        show_pairing(token, origins, args.port, workspace_url=url)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        if not args.no_browser:
            # Only open the static page: tokens are never included in URLs.
            threading.Thread(target=webbrowser.open, args=(url,), daemon=True).start()
        uvicorn.run(app, host='127.0.0.1', port=args.port, workers=1,
                    access_log=False, proxy_headers=False, server_header=False, ws='none',
                    log_level='warning')
    except (OSError, RuntimeError, ValueError) as error:
        print('Cannot start the local workspace: {}'.format(error), file=sys.stderr)
        return 2
    finally:
        if 'thread' in locals():
            server.shutdown()
            thread.join(timeout=5)
        server.server_close()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
