#!/usr/bin/env python3
"""Replay archive integrity and the complete bounded exact regression suite."""
from __future__ import annotations
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main() -> None:
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    for script in ('verify_manifest.py', 'tests/run_tests.py', 'tests/cli_smoke.py'):
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, env=env, check=True)
    print(json.dumps({'status': 'PASS', 'event': 'archive_replay',
                      'scope': 'integrity and finite regression checks; no Lean or external review'}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (OSError, subprocess.CalledProcessError) as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        raise SystemExit(1)
