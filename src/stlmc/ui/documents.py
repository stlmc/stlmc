"""Managed model/config files, with atomic writes and revision checks."""
import hashlib
import os
import tempfile
import threading
from pathlib import Path
from typing import Literal, Optional

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field
from .paths import data_dir

DIRECTORY = Path(os.environ.get('STLMC_WEB_MODELS', str(data_dir() / 'models'))).resolve()
LOCK = threading.RLock()
router = APIRouter(prefix='/api/documents')


class SaveRequest(BaseModel):
    text: str = Field(max_length=500_000)
    revision: Optional[str] = Field(default=None, max_length=64)


def file_path(name):
    if (not name or len(name) > 200 or name.startswith('.') or '/' in name or '\\' in name
            or '\x00' in name or Path(name).suffix not in {'.model', '.cfg'}):
        raise HTTPException(422, 'Use a filename ending in .model or .cfg, without directories.')
    path = DIRECTORY / name
    if path.is_symlink() or path.resolve().parent != DIRECTORY.resolve():
        raise HTTPException(422, 'File must be inside the model folder.')
    return path


def read_document(name):
    with LOCK:
        path = file_path(name)
        if not path.is_file():
            raise HTTPException(404, 'File not found')
        data = path.read_bytes()
        if len(data) > 2_000_000:
            raise HTTPException(413, 'File is too large to edit')
        try:
            text = data.decode('utf-8')
        except UnicodeError:
            raise HTTPException(422, 'File must be UTF-8 text')
        return {'name': name, 'text': text, 'revision': hashlib.sha256(data).hexdigest()}


@router.get('')
def list_documents(kind: Literal['model', 'cfg'] = 'model'):
    if not DIRECTORY.is_dir():
        return []
    with LOCK:
        return [{'name': p.name} for p in sorted(DIRECTORY.glob('*.' + kind))
                if p.is_file() and not p.is_symlink() and not p.name.startswith('.')]


@router.get('/{name}')
def get_document(name: str):
    return read_document(name)


@router.put('/{name}')
def save_document(name: str, request: SaveRequest):
    with LOCK:
        DIRECTORY.mkdir(parents=True, exist_ok=True)
        path = file_path(name)
        if path.suffix == '.cfg' and len(request.text) > 100_000:
            raise HTTPException(413, 'Config must be smaller than 100,000 characters')
        if path.exists():
            current = read_document(name)
            if request.revision != current['revision']:
                raise HTTPException(409, 'File already exists or changed since loading. Reload it, or save under a different filename.')
        elif request.revision is not None:
            raise HTTPException(409, 'File was removed since loading. Reload or save under a different filename.')
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=DIRECTORY,
                                             prefix='.save-', delete=False) as stream:
                temporary = Path(stream.name)
                stream.write(request.text)
            temporary.replace(path)
        finally:
            if temporary and temporary.exists():
                temporary.unlink()
        return read_document(name)
