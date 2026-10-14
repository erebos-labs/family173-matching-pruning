"""Verify all packaged SHA256 hashes and reject unlisted files. No network."""
from __future__ import annotations
import hashlib
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = root / 'MANIFEST.sha256'
    names = set()
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest, name = line.split('  ', 1)
        if len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
            raise ValueError('invalid digest')
        rel = Path(name)
        if rel.is_absolute() or '..' in rel.parts or name in names or name == manifest.name:
            raise ValueError('invalid or duplicate manifest path: ' + name)
        path = root / rel
        if path.is_symlink() or root not in path.resolve().parents or not path.is_file():
            raise ValueError('invalid payload file: ' + name)
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('hash mismatch: ' + name)
        names.add(name)
    actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
    if actual != names | {manifest.name}:
        raise ValueError('unlisted or missing payload files: ' + str(actual ^ (names | {manifest.name})))
    print('PASS: manifest verified;', len(names), 'hashed files; no unlisted files.')


if __name__ == '__main__':
    main()
