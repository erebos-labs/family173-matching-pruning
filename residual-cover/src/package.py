"""Deterministic local packaging; writes only this sibling handoff's manifest/ZIP."""
import argparse
import hashlib
from pathlib import Path
import zipfile


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=root.parent / (root.name + '.zip'))
    args = parser.parse_args()
    target = args.output.resolve()
    if target.is_relative_to(root.resolve()):
        raise ValueError('ZIP must be outside the payload directory')
    paths = sorted(p for p in root.rglob('*') if p.is_file()
                   and '__pycache__' not in p.parts and p.relative_to(root).as_posix() != 'MANIFEST.sha256')
    if any(p.is_symlink() for p in paths):
        raise ValueError('symlink in payload')
    lines = [hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(root).as_posix() for p in paths]
    manifest = root / 'MANIFEST.sha256'
    manifest.write_text('\n'.join(lines) + '\n')
    paths = sorted(paths + [manifest])
    with zipfile.ZipFile(target, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in paths:
            entry = zipfile.ZipInfo(root.name + '/' + p.relative_to(root).as_posix(), (2026, 10, 14, 0, 0, 0))
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            entry.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(entry, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    digest = hashlib.sha256(target.read_bytes()).hexdigest()
    target.with_suffix(target.suffix + '.sha256').write_text(digest + '  ' + target.name + '\n')
    print('ZIP', target.name, 'files=', len(paths), 'bytes=', target.stat().st_size)
    print('SHA256', digest)


if __name__ == '__main__':
    main()
