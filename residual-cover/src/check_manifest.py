"""Read-only integrity check for the selected public addendum and pinned source."""
import hashlib
from pathlib import Path

BLOB = '4fe3b01285d67d6fb5a5e7a8798a3c12f432ff76'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def payload(root):
    return sorted(p for p in root.rglob('*') if p.is_file()
                  and '__pycache__' not in p.parts and p.relative_to(root).as_posix() != 'MANIFEST.sha256')


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = root / 'MANIFEST.sha256'
    rows = {}
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = root / name
        if (name in rows or path.is_symlink() or not path.resolve().is_relative_to(root.resolve())
                or not path.is_file() or sha(path.read_bytes()) != digest):
            raise ValueError('invalid manifest entry: ' + name)
        rows[name] = digest
    expected = {p.relative_to(root).as_posix() for p in payload(root)}
    if set(rows) != expected:
        raise ValueError('manifest inventory differs from actual payload')
    raw = (root / 'sources/02-pruning.pinned.tex').read_bytes()
    blob = hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest()
    if blob != BLOB:
        raise ValueError('pinned Git blob mismatch')
    print('PASS', len(rows), 'payload checksums and exact manifest inventory;')
    print('PASS pinned source:', len(raw), 'bytes, Git blob', blob)


if __name__ == '__main__':
    main()
