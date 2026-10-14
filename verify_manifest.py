#!/usr/bin/env python3
"""Check payload hashes, SHA256SUMS, and exact retained source Git blobs.

Public v1.0.1 modification: exclude .git metadata from payload enumeration.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

ROOT = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def safe_file(name: str) -> Path:
    require(type(name) is str, 'manifest path is not text')
    path = PurePosixPath(name)
    require(not path.is_absolute() and '..' not in path.parts and str(path) == name,
            'unsafe or noncanonical manifest path: ' + name)
    actual = ROOT.joinpath(*path.parts)
    require(actual.is_file() and not actual.is_symlink(), 'missing/nonregular file: ' + name)
    require(actual.resolve().is_relative_to(ROOT), 'path escapes archive: ' + name)
    return actual


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text(encoding='utf-8'))
    require(manifest.get('schema') == 'family173.manifest.v1', 'manifest schema')
    items = manifest.get('files')
    require(isinstance(items, list), 'manifest file list')
    found = set()
    for item in items:
        name = item['path']
        require(name not in found and name not in {'MANIFEST.json', 'SHA256SUMS'},
                'duplicate or circular manifest entry: ' + name)
        found.add(name)
        path = safe_file(name)
        require(path.stat().st_size == item['bytes'], 'file size mismatch: ' + name)
        require(sha256(path) == item['sha256'], 'SHA-256 mismatch: ' + name)
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*')
              if p.is_file() and '__pycache__' not in p.parts and '.git' not in p.parts and p.name != '.DS_Store'}
    require(actual == found | {'MANIFEST.json', 'SHA256SUMS'}, 'missing or unexpected payload files')
    sums = {}
    for line in (ROOT / 'SHA256SUMS').read_text(encoding='utf-8').splitlines():
        digest, name = line.split('  ', 1)
        require(name not in sums, 'duplicate SHA256SUMS entry')
        sums[name] = digest
        require(sha256(safe_file(name)) == digest, 'SHA256SUMS mismatch: ' + name)
    require(set(sums) == found | {'MANIFEST.json'}, 'SHA256SUMS coverage mismatch')
    sources = json.loads((ROOT / 'provenance/SOURCE_HASHES.json').read_text(encoding='utf-8'))
    for item in sources['snapshots']:
        raw = safe_file(item['local_path']).read_bytes()
        header = b'blob ' + str(len(raw)).encode('ascii') + b'\0'
        require(hashlib.sha1(header + raw).hexdigest() == item['git_blob_sha1'],
                'upstream Git blob mismatch: ' + item['local_path'])
        require(hashlib.sha256(raw).hexdigest() == item['sha256'] and len(raw) == item['bytes'],
                'upstream raw-byte mismatch: ' + item['local_path'])
    print(json.dumps({'status': 'PASS', 'payload_files': len(found),
                      'source_snapshot_checks': len(sources['snapshots']),
                      'scope': 'byte integrity and recorded source identity, not a mathematical proof'}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        raise SystemExit(1)
