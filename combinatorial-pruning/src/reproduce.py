"""Syntax-check and regenerate all fixtures under two Python hash seeds.

All writes are confined to a temporary directory. Mathematical verification
is performed by verify.py, not by trusting byte reproducibility alone.
"""
from __future__ import annotations
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    root = Path(__file__).resolve().parents[1]
    scripts = sorted((root / 'src').glob('*.py'))
    for script in scripts:
        compile(script.read_text(encoding='utf-8'), str(script), 'exec')
    print('syntax_checked_python_files', len(scripts), flush=True)
    names = sorted(p.name for p in (root / 'fixtures').glob('*.json'))
    if len(names) != 11:
        raise ValueError('expected eleven baseline fixtures')
    for seed in ['0', '1']:
        with tempfile.TemporaryDirectory(prefix='family173-reproduce-') as temp:
            output = Path(temp) / 'fixtures'
            env = dict(os.environ, PYTHONHASHSEED=seed, PYTHONDONTWRITEBYTECODE='1')
            result = subprocess.run([sys.executable, '-B', str(root / 'src/producer.py'),
                                     '--output', str(output)], env=env, text=True,
                                    capture_output=True, check=True)
            print(result.stdout, end='', flush=True)
            if sorted(p.name for p in output.glob('*.json')) != names:
                raise ValueError('regenerated fixture filenames differ')
            for name in names:
                original = (root / 'fixtures' / name).read_bytes()
                regenerated = (output / name).read_bytes()
                if original != regenerated:
                    raise ValueError('fixture differs: ' + name + ', hash seed ' + seed)
            result = subprocess.run([sys.executable, '-B', str(root / 'src/verify.py'),
                                     '--fixtures', str(output)], env=env, text=True,
                                    capture_output=True, check=True)
            print(result.stdout, end='', flush=True)
            print('byte_identical_fixtures', len(names), 'hash_seed', seed, flush=True)
    digest = hashlib.sha256()
    for name in names:
        digest.update(name.encode() + b'\0' + (root / 'fixtures' / name).read_bytes())
    print('fixture_stream_sha256', digest.hexdigest())
    print('PASS: syntax checks and deterministic fixture regeneration.')


if __name__ == '__main__':
    main()
