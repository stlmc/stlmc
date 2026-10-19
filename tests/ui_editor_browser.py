"""Optional real-browser editor geometry regression (no browser download).

Set STLMC_TEST_BROWSER_EXECUTABLE to a Playwright-compatible Chromium binary.
Requires the developer-only playwright package and generated UI assets.
"""
import functools
from http.server import ThreadingHTTPServer
import json
import os
from pathlib import Path
import sys
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from stlmc.ui.static_server import StaticAssetHandler


class EditorGeometryTest(unittest.IsolatedAsyncioTestCase):
    async def test_visible_line36_click_and_delete_leave_line37_untouched(self):
        binary = os.environ.get('STLMC_TEST_BROWSER_EXECUTABLE')
        if not binary:
            self.skipTest('Set STLMC_TEST_BROWSER_EXECUTABLE for optional browser tests')
        try:
            from playwright.async_api import async_playwright
        except ImportError:
            self.skipTest('Developer-only playwright package is not installed')
        static = ROOT / 'src/stlmc/ui/static'
        if not (static / 'index.html').is_file():
            self.skipTest('Generate frontend assets with python tools/build_ui.py')
        server = ThreadingHTTPServer(('127.0.0.1', 0),
            functools.partial(StaticAssetHandler, directory=static))
        thread = threading.Thread(target=server.serve_forever,
                                  kwargs={'poll_interval': .01}, daemon=True)
        thread.start()
        try:
            async with async_playwright() as playwright:
                browser = await playwright.chromium.launch(executable_path=binary, headless=True)
                try:
                    page = await browser.new_page(viewport={'width': 1500, 'height': 1000})
                    errors = []
                    page.on('pageerror', lambda error: errors.append(str(error)))
                    await page.goto('http://127.0.0.1:{}/'.format(server.server_port), wait_until='networkidle')
                    text = '\n'.join(['# configuration line ' + str(i) for i in range(1, 34)] +
                                     ['yices {', '    # Linear real arithmetic.',
                                      '    logic = "QF_LRA"', '}']) + '\n'
                    for kind in ('model', 'config'):
                        editor = page.locator('#' + kind)
                        await editor.evaluate('(e, text) => {e.value = text; e.dispatchEvent(new Event("input"));}', text)
                        content = page.locator('#' + kind + '-pane .cm-content')
                        await content.click()
                        await content.press('Control+End')
                        await page.wait_for_timeout(300)
                        point = await content.evaluate('''async e => {
                          const {EditorView} = await import('/js/codemirror.js');
                          const view = EditorView.findFromDOM(e);
                          const line = view.state.doc.line(36);
                          const rect = view.coordsAtPos(line.from + 4);
                          return {x: rect.left, y: (rect.top + rect.bottom) / 2};
                        }''')
                        await page.mouse.click(point['x'] + .1, point['y'])
                        expected = sum(len(line) + 1 for line in text.split('\n')[:35]) + 4
                        position = await content.evaluate('''async e => {
                          const {EditorView} = await import('/js/codemirror.js');
                          return EditorView.findFromDOM(e).state.selection.main.head;
                        }''')
                        self.assertEqual(position, expected, kind)
                        await content.press('Delete')
                        lines = (await editor.evaluate('e => e.value')).splitlines()
                        self.assertEqual(lines[35], '    ogic = "QF_LRA"', kind)
                        self.assertEqual(lines[36], '}', kind)
                    await page.evaluate('''async () => {
                      const {installEditor} = await import('/js/editor.js');
                      const area = document.createElement('textarea');
                      area.value = 'common {\\nthreshold=0.1\\n};';
                      const parent = document.createElement('div'); parent.id = 'editor-test';
                      document.body.append(parent); parent.append(area);
                      const editor = installEditor(area, 'test');
                      // Real input handlers immediately clear old parser errors.
                      area.oninput = () => editor.setDiagnostics([]);
                      editor.setDiagnostics([{line: 3, column: 2, message: "unexpected ';'"}]);
                      window.editorTest = {area, editor};
                    }''')
                    issue = page.locator('#test-problems button')
                    self.assertEqual(await issue.inner_text(), "Line 3, column 2: unexpected ';'")
                    await issue.click()
                    self.assertEqual(await page.evaluate('''async () => {
                      const {EditorView} = await import('/js/codemirror.js');
                      const view = EditorView.findFromDOM(document.querySelector('#editor-test .cm-content'));
                      const selection = view.state.selection.main;
                      return view.state.sliceDoc(selection.from, selection.to);
                    }'''), ';')
                    content = page.locator('#editor-test .cm-content')
                    await content.press('Backspace')
                    await page.wait_for_timeout(50)
                    self.assertTrue(await page.locator('#test-problems').is_hidden())
                    self.assertEqual(await page.evaluate('window.editorTest.area.value'), 'common {\nthreshold=0.1\n}')
                    await content.press('Control+z')
                    self.assertTrue((await page.evaluate('window.editorTest.area.value')).endswith('};'))
                    await page.evaluate("window.editorTest.area.value = 'new document'")
                    await content.press('Control+z')
                    self.assertEqual(await page.evaluate('window.editorTest.area.value'), 'new document')
                    # The local no-auth mode hides the token and auto-connects;
                    # hosted/default pages still use the authenticated flow.
                    async def local_connection(route):
                        await route.fulfill(content_type='application/json', body=json.dumps({
                            'bridge_url': 'http://127.0.0.1:' + str(server.server_port),
                            'auth_required': False}))
                    async def api(route):
                        path = route.request.url.split('/api/', 1)[1].split('?', 1)[0]
                        body = {'bridge': {'protocol': 1, 'version': 'test', 'auth_required': False},
                                'health': {'stlmc': True},
                                'inspect': {'common': {'solver': 'auto'}, 'goals': [],
                                            'diagnostics': [], 'solver_choices': ['auto', 'z3']}}
                        await route.fulfill(content_type='application/json', body=json.dumps(body.get(path, [])))
                    await page.route('**/local-connection.json', local_connection)
                    await page.route('**/api/**', api)
                    await page.reload(wait_until='networkidle')
                    await page.wait_for_function("document.getElementById('runtime-state').textContent === 'Connected'")
                    self.assertTrue(await page.locator('#token-field').is_hidden())
                    self.assertEqual(await page.locator('#solver').input_value(), 'auto')
                    self.assertEqual(errors, [])
                finally:
                    await browser.close()
        finally:
            server.shutdown(); server.server_close(); thread.join(timeout=5)


if __name__ == '__main__':
    unittest.main()
