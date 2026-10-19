"""Conservative component removal; system packages and user outputs are retained."""
from dataclasses import dataclass, field
import errno
import hashlib
from importlib.metadata import distribution, PackageNotFoundError
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys

from ..solver.availability import solver_data_dir
from .install_receipts import file_hash, RECEIPT_NAME


@dataclass
class NativeRemoval:
    path: Path
    sha256: str
    root: Path
    role: str = 'native'


@dataclass
class UninstallPlan:
    packages: list = field(default_factory=list)
    removals: list = field(default_factory=list)
    notes: list = field(default_factory=list)


def _no_symlinks(path):
    path = Path(path).absolute()
    return '..' not in path.parts and path.resolve() == path and not path.is_symlink()


def _receipt_removals(root, receipt, kind, notes):
    if not _no_symlinks(root) or not _no_symlinks(receipt) or not receipt.is_file():
        notes.append('Preserved {}: no safe installer ownership receipt; remove manually if appropriate.'.format(root))
        return []
    try:
        record = json.loads(receipt.read_text())
        files = record['files']
        if (record.get('schema') != 1 or record.get('managed_by') != 'stlmc-installer'
                or record.get('kind') != kind or record.get('root') != str(root)
                or not isinstance(files, dict) or not files):
            raise ValueError('invalid receipt identity')
        if kind == 'dreal-managed' and set(files) != {'dReal'}:
            raise ValueError('dReal receipt may only own its fixed executable')
        result = []
        retained = False
        for relative, digest in files.items():
            name = PurePosixPath(relative)
            if (not relative or name.is_absolute() or '..' in name.parts or str(name) == '.'
                    or relative == RECEIPT_NAME or not isinstance(digest, str)
                    or not re.fullmatch('[0-9a-f]{64}', digest)):
                raise ValueError('invalid inventory path or hash')
            path = root.joinpath(*name.parts)
            if not _no_symlinks(path):
                raise ValueError('symlink in inventory path')
            if not path.exists():
                notes.append('Already absent: ' + str(path))
                continue
            if not path.is_file() or file_hash(path) != digest:
                notes.append('Changed file preserved: ' + str(path))
                retained = True
                continue
            result.append(NativeRemoval(path, digest, root))
        if kind == 'yices-official':
            for path in root.rglob('*'):
                if ((path.is_file() or path.is_symlink()) and path != receipt
                        and str(path.relative_to(root)) not in files):
                    notes.append('Unrecorded file preserved: ' + str(path))
                    retained = True
        if retained:
            notes.append('Ownership receipt retained for remaining user files: ' + str(receipt))
        else:
            result.append(NativeRemoval(receipt, file_hash(receipt), root, 'receipt'))
        return result
    except (OSError, ValueError, TypeError, KeyError) as error:
        notes.append('Preserved {}: invalid ownership receipt ({}).'.format(root, error))
        return []


def plan_uninstall(solvers, visuals, ui=False):
    plan = UninstallPlan()
    packages = {'z3': 'z3-solver', 'cvc5': 'cvc5', 'yices': 'yices'}
    requested = [packages[name] for name in solvers if name in packages]
    requested += [name for output, name in (('html', 'bokeh'), ('pdf', 'matplotlib')) if output in visuals]
    if ui:
        from .dependency_policy import UI_UNINSTALL_PACKAGES
        requested += list(UI_UNINSTALL_PACKAGES)
        plan.notes.append('Retained UI models, run results, and shared dependencies, including packaging.')
    prefix = Path(sys.prefix).resolve()
    for package in requested:
        try:
            installed = distribution(package)
        except PackageNotFoundError:
            plan.notes.append('{}: not installed; nothing to remove.'.format(package))
            continue
        location = Path(installed.locate_file('')).resolve()
        if sys.prefix == sys.base_prefix or prefix not in location.parents:
            plan.notes.append('Preserved {} outside the active virtual environment ({}).'.format(package, location))
        else:
            plan.packages.append(package)
    if visuals:
        plan.notes.append('Retained STLmc base packages and shared dependencies, including numpy and scipy.')
    data = solver_data_dir().absolute()
    if 'yices' in solvers:
        base = data / 'yices'
        active = base / 'active.json'
        if active.exists() or active.is_symlink():
            if _no_symlinks(active) and active.is_file():
                plan.removals.append(NativeRemoval(active, file_hash(active), base, 'activation'))
                plan.notes.append('Yices activation will be removed; legacy/custom-prefix files without receipts are retained.')
                try:
                    prefix = json.loads(active.read_text()).get('prefix')
                    if isinstance(prefix, str) and base / 'releases' not in Path(prefix).parents:
                        plan.notes.append('Custom/source-build native prefix retained for manual review: ' + prefix)
                except (ValueError, AttributeError):
                    pass
            else:
                plan.notes.append('Preserved unsafe Yices activation path; remove the selection manually.')
        releases = base / 'releases'
        explicit = os.environ.get('STLMC_YICES_LIBRARY')
        if explicit:
            plan.notes.append('STLMC_YICES_LIBRARY is not changed; its explicitly selected library is preserved.')
        if _no_symlinks(releases) and releases.is_dir():
            for root in sorted(releases.iterdir()):
                if not re.fullmatch(r'yices-\d+(?:\.\d+)*-[0-9a-f]{32}', root.name):
                    continue
                if explicit and root.resolve() in Path(explicit).expanduser().resolve().parents:
                    plan.notes.append('Preserved explicitly selected installation: ' + str(root))
                    continue
                plan.removals.extend(_receipt_removals(root, root / RECEIPT_NAME,
                                                       'yices-official', plan.notes))
    if 'dreal' in solvers:
        root = data / 'dReal3'
        target = root / 'dReal'
        if target.exists() or target.is_symlink():
            receipts = root / '.stlmc-receipts'
            if _no_symlinks(target) and target.is_file() and _no_symlinks(receipts):
                receipt = receipts / ('dreal-' + file_hash(target) + '.json')
                plan.removals.extend(_receipt_removals(root, receipt, 'dreal-managed', plan.notes))
            else:
                plan.notes.append('Preserved dReal without a safe ownership receipt; remove manually if appropriate.')
        plan.notes.append('External/PATH dReal executables and source-build directories are never removed.')
    return plan


def _open_parent(path):
    """Anchor every parent directory without following any symlinks."""
    if (os.name != 'posix' or not hasattr(os, 'O_NOFOLLOW')
            or os.open not in os.supports_dir_fd or os.unlink not in os.supports_dir_fd):
        raise RuntimeError('Safe native removal requires POSIX dir_fd/O_NOFOLLOW support')
    path = Path(path).absolute()
    if '..' in path.parts or len(path.parts) < 2:
        raise RuntimeError('Unsafe native removal path')
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    descriptor = os.open(path.anchor, flags)
    try:
        for component in path.parts[1:-1]:
            child = os.open(component, flags, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        return descriptor, path.name
    except BaseException:
        os.close(descriptor)
        raise


def _remove_verified(item):
    try:
        parent, name = _open_parent(item.path)
    except FileNotFoundError:
        return True
    try:
        try:
            descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent)
        except FileNotFoundError:
            return True
        try:
            before = os.fstat(descriptor)
            if not stat.S_ISREG(before.st_mode):
                raise RuntimeError('Not a regular managed file: ' + str(item.path))
            digest = hashlib.sha256()
            for chunk in iter(lambda: os.read(descriptor, 1024 * 1024), b''):
                digest.update(chunk)
            current = os.stat(name, dir_fd=parent, follow_symlinks=False)
            if (digest.hexdigest() != item.sha256
                    or (current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns)
                    != (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)):
                raise RuntimeError('Changed file preserved: ' + str(item.path))
            os.unlink(name, dir_fd=parent)
            return True
        finally:
            os.close(descriptor)
    finally:
        os.close(parent)


def execute_uninstall(plan, dry_run=False):
    for note in plan.notes:
        print(note)
    for package in plan.packages:
        print(('Would uninstall pip package: ' if dry_run else 'Uninstalling pip package: ') + package)
    for item in plan.removals:
        print(('Would remove ' if dry_run else 'Removing ') + item.role + ': ' + str(item.path))
    if dry_run:
        return 0
    failed = False
    # Deactivate first: a partial file-removal failure must not leave a manifest
    # pointing to a partially removed library. Remaining files are reported.
    for item in (item for item in plan.removals if item.role == 'activation'):
        try:
            _remove_verified(item)
        except (OSError, RuntimeError) as error:
            print('Native removal aborted: ' + str(error), file=sys.stderr)
            return 1
    changed_roots = set()
    for item in (item for item in plan.removals if item.role != 'activation'):
        if item.role == 'receipt' and item.root in changed_roots:
            continue
        try:
            _remove_verified(item)
        except (OSError, RuntimeError) as error:
            print(str(error) + '; retained for manual review.', file=sys.stderr)
            changed_roots.add(item.root)
            failed = True
    directories = set()
    for item in plan.removals:
        if item.role == 'activation':
            continue
        parent = item.path.parent
        while parent == item.root or item.root in parent.parents:
            directories.add(parent)
            if parent == item.root:
                break
            parent = parent.parent
    for directory in sorted(directories, key=lambda path: len(path.parts), reverse=True):
        try:
            parent, name = _open_parent(directory)
            try:
                os.rmdir(name, dir_fd=parent)
            finally:
                os.close(parent)
        except OSError as error:
            if error.errno not in (errno.ENOTEMPTY, errno.EEXIST, errno.ENOENT):
                print('Could not remove empty managed directory {}: {}'.format(directory, error), file=sys.stderr)
                failed = True
        except RuntimeError as error:
            print(str(error), file=sys.stderr)
            failed = True
    if plan.packages:
        try:
            subprocess.run([sys.executable, '-m', 'pip', 'uninstall', '--yes', *plan.packages], check=True)
        except (OSError, subprocess.SubprocessError) as error:
            print('pip uninstall failed: ' + str(error), file=sys.stderr)
            failed = True
    return int(failed)
