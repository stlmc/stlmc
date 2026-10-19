"""File-level ownership records for future conservative native uninstalls."""
import hashlib
import json
import os
from pathlib import Path
import tempfile


RECEIPT_NAME = '.stlmc-install.json'


def file_hash(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def write_receipt(root, kind, files=None, receipt_path=None):
    root = Path(root).absolute()
    if files is None:
        files = {str(path.relative_to(root)): path for path in root.rglob('*')
                 if path.is_file() and not path.is_symlink() and path.name != RECEIPT_NAME}
    receipt = dict(schema=1, managed_by='stlmc-installer', kind=kind,
                   root=str(root), files={name: file_hash(path) for name, path in files.items()})
    target = Path(receipt_path) if receipt_path is not None else root / RECEIPT_NAME
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=str(target.parent),
                                     prefix='receipt-', delete=False) as stream:
        json.dump(receipt, stream, indent=2)
        staged = Path(stream.name)
    try:
        os.replace(staged, target)
    finally:
        if staged.exists():
            staged.unlink()
    return target


def write_dreal_receipt(staged, target):
    target = Path(target).absolute()
    digest = file_hash(staged)
    receipt = target.parent / '.stlmc-receipts' / ('dreal-' + digest + '.json')
    # A new content-addressed receipt does not overwrite ownership evidence for
    # the previous executable if publishing the newly staged executable fails.
    return write_receipt(target.parent, 'dreal-managed', {'dReal': Path(staged)}, receipt)
