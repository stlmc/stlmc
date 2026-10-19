"""Writable UI state is separate from installed, read-only package assets."""
import os
from pathlib import Path
import sys


def data_dir():
    if sys.platform == 'darwin':
        base = Path.home() / 'Library' / 'Application Support'
    else:
        base = Path(os.environ.get('XDG_DATA_HOME', Path.home() / '.local' / 'share'))
    return base / 'stlmc' / 'ui'


def seed_examples(directory):
    """Copy packaged examples once, never replacing user edits."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    examples = Path(__file__).with_name('static') / 'examples'
    for source in sorted(examples.iterdir()):
        if source.suffix not in {'.model', '.cfg'} or not source.is_file():
            continue
        try:
            with (directory / source.name).open('xb') as target:
                target.write(source.read_bytes())
        except FileExistsError:
            pass
