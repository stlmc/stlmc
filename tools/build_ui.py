"""Regenerate checked-in UI assets; Ruby is a development-only prerequisite."""
import argparse
import hashlib
import os
from pathlib import Path, PurePosixPath
import re
import runpy
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src/stlmc/ui/frontend'
STATIC = ROOT / 'src' / 'stlmc' / 'ui' / 'static'
MANIFEST = STATIC.parent / 'static_server.py'
MAX_ASSET_SIZE = 4 * 1024 * 1024
MAX_TOTAL_SIZE = 16 * 1024 * 1024


def expected_assets(manifest=MANIFEST):
    # This module uses only the standard library and starts no server. Loading
    # its explicit allowlist does not import STLmc or optional UI dependencies.
    assets = runpy.run_path(str(manifest))['ASSETS']
    names = set()
    if not isinstance(assets, dict) or not assets:
        raise ValueError('Static server asset allowlist must be a nonempty mapping')
    for value in assets.values():
        if not isinstance(value, tuple) or len(value) != 2 or not isinstance(value[0], str):
            raise ValueError('Invalid static server asset declaration')
        name = value[0]
        path = PurePosixPath(name)
        if (not name or path.is_absolute() or not re.fullmatch(r'[A-Za-z0-9_./-]+', name)
                or any(part.startswith('.') for part in path.parts)
                or path.as_posix() != name):
            raise ValueError('Unsafe static asset path: ' + name)
        names.add(name)
    if not {'index.html', 'app.js', 'styles.css'} <= names:
        raise ValueError('Static server allowlist is missing required UI entry assets')
    return names


def inventory(directory):
    """Reject links and nonregular files before reading generated/public data."""
    directory = Path(directory)
    if directory.is_symlink() or directory.resolve() != directory.absolute():
        raise ValueError('UI asset root must not contain symlinks: ' + str(directory))
    if not directory.exists():
        return {}
    result, total = {}, 0
    for path in sorted(directory.rglob('*')):
        info = path.lstat()
        if stat.S_ISDIR(info.st_mode):
            continue
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise ValueError('UI assets must be single-link regular files: ' + str(path))
        total += info.st_size
        if info.st_size > MAX_ASSET_SIZE or total > MAX_TOTAL_SIZE:
            raise ValueError('UI asset size limit exceeded')
        result[path.relative_to(directory).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def compare(generated, installed, names):
    actual = inventory(generated)
    if set(actual) != names:
        raise ValueError('Jekyll output differs from the static allowlist: missing={}, unexpected={}'.format(
            sorted(names - actual.keys()), sorted(actual.keys() - names)))
    current = inventory(installed)
    return {
        'missing': sorted(names - current.keys()),
        'unexpected': sorted(current.keys() - names),
        'changed': sorted(name for name in names & current.keys() if current[name] != actual[name]),
    }


def synchronize(generated, installed, names):
    """Replace generated assets only; never recursively delete unknown files."""
    differences = compare(generated, installed, names)
    if differences['unexpected']:
        raise ValueError('Unrecognized files in bundled static directory; review them manually: ' +
                         ', '.join(differences['unexpected']))
    for name in differences['missing'] + differences['changed']:
        target = installed / name
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(dir=target.parent, prefix='.ui-build-', delete=False) as output:
                temporary = Path(output.name)
                output.write((generated / name).read_bytes())
            temporary.chmod(0o644)
            temporary.replace(target)
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    return differences


def build(destination, source=SOURCE):
    if not (source / 'Gemfile').is_file() or not (source / 'Gemfile.lock').is_file():
        raise ValueError('UI development Gemfile and Gemfile.lock are required')
    environment = dict(os.environ, BUNDLE_GEMFILE=str(source / 'Gemfile'),
                       BUNDLE_FROZEN='true', JEKYLL_ENV='production', TZ='UTC')
    command = ['bundle', 'exec', 'jekyll', 'build', '--source', str(source),
               '--destination', str(destination), '--safe', '--disable-disk-cache']
    try:
        result = subprocess.run(command, cwd=source, env=environment,
                                capture_output=True, text=True, timeout=120)
    except FileNotFoundError:
        raise RuntimeError('UI regeneration requires Ruby and Bundler. Ordinary pip installation does not. '
                           'Install development gems with: cd src/stlmc/ui/frontend && bundle install') from None
    if result.returncode:
        raise RuntimeError('Jekyll UI build failed. Run `cd src/stlmc/ui/frontend && bundle install` first.\n' +
                           result.stdout + result.stderr)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
                        help='build into .tmp and fail on drift, without changing checked-in assets')
    args = parser.parse_args(argv)
    try:
        names = expected_assets()
        temporary_root = ROOT / '.tmp'
        if temporary_root.is_symlink():
            raise ValueError('The repository .tmp directory must not be a symlink')
        temporary_root.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='ui-build-', dir=temporary_root) as temporary:
            output = Path(temporary) / 'site'
            build(output)
            differences = compare(output, STATIC, names)
            if args.check:
                if any(differences.values()):
                    print('Bundled UI assets are stale: ' + str(differences), file=sys.stderr)
                    print('Regenerate with: python tools/build_ui.py', file=sys.stderr)
                    return 1
            else:
                synchronize(output, STATIC, names)
        print('UI assets {} ({} files).'.format('match Jekyll sources' if args.check else 'regenerated', len(names)))
        return 0
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
