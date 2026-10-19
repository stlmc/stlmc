"""UI build checks need neither Ruby nor optional Python UI dependencies."""
import importlib.util
import io
import os
from pathlib import Path
import runpy
import shlex
import subprocess
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('ui_build_tool', ROOT / 'tools' / 'build_ui.py')
TOOL = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOL)


class UiBuildTest(unittest.TestCase):
    def test_wheel_build_generates_ui_before_collecting_package_data(self):
        if importlib.util.find_spec('setuptools') is None:
            self.skipTest('Build-hook test requires the source-build dependency setuptools')
        with mock.patch('setuptools.setup'):
            setup = runpy.run_path(str(ROOT / 'setup.py'))
        events = []
        with tempfile.TemporaryDirectory() as temporary:
            from setuptools import Distribution
            command = setup['BuildWithRevision'](Distribution())
            command.build_lib = temporary
            with mock.patch.object(setup['subprocess'], 'run',
                                   side_effect=lambda *args, **kwargs: events.append(('generate', args, kwargs))), \
                    mock.patch.dict(command.run.__globals__, write_build_info=mock.Mock()), \
                    mock.patch('setuptools.command.build_py.build_py.run',
                               side_effect=lambda: events.append(('collect',))):
                command.run()
        self.assertEqual([event[0] for event in events], ['generate', 'collect'])
        self.assertEqual(events[0][1][0][1], str(ROOT / 'tools' / 'build_ui.py'))
        self.assertTrue(events[0][2]['check'])

    def fixture(self, root, name, data='fixture'):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(data)
        return path

    def test_manifest_is_the_server_allowlist_without_optional_imports(self):
        names = TOOL.expected_assets()
        self.assertEqual(len(names), 11)
        self.assertIn('js/connection.js', names)
        self.assertIn('examples/therm-tutorial.model', names)
        self.assertNotIn('/', names)

    def test_source_distribution_includes_preferred_ui_sources_and_builder(self):
        included = set()
        for line in (ROOT / 'MANIFEST.in').read_text().splitlines():
            fields = shlex.split(line, comments=True)
            if fields and fields[0] == 'include':
                included.update(path for pattern in fields[1:] for path in ROOT.glob(pattern))
            elif fields and fields[0] == 'recursive-include':
                included.update(path for pattern in fields[2:]
                                for path in (ROOT / fields[1]).rglob(pattern))
        sources = {ROOT / 'tools' / 'build_ui.py'}
        sources.update(path for path in (ROOT / 'src' / 'stlmc' / 'ui' / 'frontend').rglob('*') if path.is_file() and
                       not {'.bundle', '.jekyll-cache', 'vendor', '_site'} & set(path.relative_to(ROOT / 'src' / 'stlmc' / 'ui' / 'frontend').parts) and
                       (path.suffix in {'.html', '.scss', '.js', '.model', '.cfg', '.yml'} or
                        path.name in {'Gemfile', 'Gemfile.lock'}))
        self.assertTrue(sources)
        self.assertFalse(sources - included, sorted(str(path.relative_to(ROOT)) for path in sources - included))
        self.assertTrue((ROOT / 'src' / 'stlmc' / 'ui' / 'frontend' / 'Gemfile.lock').is_file())
        self.assertTrue((ROOT / 'src' / 'stlmc' / 'ui' / 'frontend' / '_layouts' / 'workspace.html').is_file())
        self.assertFalse(any('.bundle' in path.parts or '.jekyll-cache' in path.parts for path in included))

    def test_manifest_rejects_unsafe_paths(self):
        for name in ('../private', '/private', '.private', 'js/../private', 'js\\private'):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temporary:
                manifest = self.fixture(Path(temporary).resolve(), 'manifest.py',
                    'ASSETS={"/":(' + repr(name) + ',"text/plain")}')
                with self.assertRaises(ValueError):
                    TOOL.expected_assets(manifest)

    def test_generated_output_must_match_allowlist_exactly(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            self.fixture(base / 'output', 'index.html')
            self.fixture(base / 'output', 'private.txt')
            with self.assertRaisesRegex(ValueError, 'unexpected'):
                TOOL.compare(base / 'output', base / 'static', {'index.html'})

    def test_links_and_nonregular_files_are_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            external = self.fixture(base, 'external', 'private')
            static = base / 'static'
            static.mkdir()
            (static / 'link').symlink_to(external)
            with self.assertRaises(ValueError):
                TOOL.inventory(static)
            (static / 'link').unlink()
            os.link(external, static / 'hardlink')
            with self.assertRaises(ValueError):
                TOOL.inventory(static)
            (static / 'hardlink').unlink()
            os.mkfifo(static / 'pipe')
            with self.assertRaises(ValueError):
                TOOL.inventory(static)

    def test_hash_drift_and_atomic_asset_replacement(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            self.fixture(base / 'output', 'index.html', 'new')
            self.fixture(base / 'output', 'js/app.js')
            self.fixture(base / 'static', 'index.html', 'old')
            names = {'index.html', 'js/app.js'}
            self.assertEqual(TOOL.compare(base / 'output', base / 'static', names),
                             {'changed': ['index.html'], 'missing': ['js/app.js'], 'unexpected': []})
            TOOL.synchronize(base / 'output', base / 'static', names)
            self.assertFalse(any(TOOL.compare(base / 'output', base / 'static', names).values()))

    def test_unknown_installed_files_are_not_deleted_or_overwritten(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            self.fixture(base / 'output', 'index.html', 'new')
            old = self.fixture(base / 'static', 'index.html', 'old')
            private = self.fixture(base / 'static', 'user.model', 'user data')
            with self.assertRaises(ValueError):
                TOOL.synchronize(base / 'output', base / 'static', {'index.html'})
            self.assertEqual(old.read_text(), 'old')
            self.assertEqual(private.read_text(), 'user data')

    def test_build_uses_locked_bundle_and_explicit_temporary_destination(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary).resolve() / 'source'
            destination = Path(temporary).resolve() / 'staging'
            self.fixture(source, 'Gemfile')
            self.fixture(source, 'Gemfile.lock')
            with mock.patch.object(TOOL.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, '', '')) as run:
                TOOL.build(destination, source)
            self.assertIn('--safe', run.call_args.args[0])
            self.assertIn(str(destination), run.call_args.args[0])
            self.assertEqual(run.call_args.kwargs['cwd'], source)
            self.assertEqual(run.call_args.kwargs['env']['BUNDLE_FROZEN'], 'true')

    def test_check_is_read_only_and_cleans_only_its_temporary_directory(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            installed = base / 'static'
            asset = self.fixture(installed, 'index.html', 'old')
            def generate(destination):
                self.fixture(destination, 'index.html', 'new')
            with mock.patch.object(TOOL, 'ROOT', base), mock.patch.object(TOOL, 'STATIC', installed), \
                    mock.patch.object(TOOL, 'expected_assets', return_value={'index.html'}), \
                    mock.patch.object(TOOL, 'build', side_effect=generate), \
                    mock.patch('sys.stderr', io.StringIO()):
                self.assertEqual(TOOL.main(['--check']), 1)
            self.assertEqual(asset.read_text(), 'old')
            self.assertEqual(list((base / '.tmp').iterdir()), [])

    def test_missing_bundler_is_a_developer_hint_not_a_runtime_requirement(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary).resolve()
            self.fixture(source, 'Gemfile')
            self.fixture(source, 'Gemfile.lock')
            with mock.patch.object(TOOL.subprocess, 'run', side_effect=FileNotFoundError), \
                    self.assertRaisesRegex(RuntimeError, 'installing a wheel does not'):
                TOOL.build(source / 'staging', source)


if __name__ == '__main__':
    unittest.main()
