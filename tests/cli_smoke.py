#!/usr/bin/env python3
"""Actual isolated-verifier, constructor CLI, and syntax smoke tests."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import py_compile
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    env.pop('PYTHONPATH', None)
    with tempfile.TemporaryDirectory(prefix='family173-standalone-') as td:
        work = Path(td)
        script = work / 'verify.py'
        shutil.copyfile(ROOT / 'src/verify.py', script)
        names = ('loop_coinciding_single', 'opposite_pairs_coinciding', 'sharp_2x2', 'grid_3')
        for name in names:
            a, b = work / 'input.json', work / 'certificate.json'
            shutil.copyfile(ROOT / 'examples' / (name + '.instance.json'), a)
            shutil.copyfile(ROOT / 'examples' / (name + '.certificate.json'), b)
            check(not (work / 'construct.py').exists(), 'constructor present in standalone directory')
            result = subprocess.run([sys.executable, '-I', str(script), str(a), str(b), '--bruteforce'],
                                    cwd=work, env=env, check=True, capture_output=True, text=True)
            print(json.dumps({'event': 'standalone_verifier', 'name': name, 'isolation_flag': '-I',
                              'constructor_present': False, 'returncode': result.returncode,
                              'result': json.loads(result.stdout)}, sort_keys=True), flush=True)
        output = work / 'regenerated.json'
        constructed = subprocess.run([sys.executable, str(ROOT / 'src/construct.py'),
                                      str(ROOT / 'examples/sharp_2x2.instance.json'), str(output)],
                                     cwd=work, env=env, check=True, capture_output=True, text=True)
        expected = ROOT / 'examples/sharp_2x2.certificate.json'
        check(output.read_bytes() == expected.read_bytes(), 'CLI certificate bytes differ')
        print(json.dumps({'event': 'constructor_cli_reproduction', 'status': 'PASS',
                          'returncode': constructed.returncode,
                          'certificate_sha256': hashlib.sha256(output.read_bytes()).hexdigest()}, sort_keys=True), flush=True)
        scripts = sorted(ROOT.rglob('*.py'))
        for i, path in enumerate(scripts):
            py_compile.compile(str(path), cfile=str(work / ('syntax-%d.pyc' % i)), doraise=True)
        print(json.dumps({'event': 'syntax_compilation', 'status': 'PASS',
                          'scripts': [p.relative_to(ROOT).as_posix() for p in scripts]}, sort_keys=True), flush=True)
    print(json.dumps({'event': 'cli_smoke', 'status': 'PASS'}, sort_keys=True))


if __name__ == '__main__':
    main()
