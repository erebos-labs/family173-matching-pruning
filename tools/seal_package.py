#!/usr/bin/env python3
"""Seal the explicit public tree. Only run after reviewing intentional changes."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
excluded={'MANIFEST.json','SHA256SUMS'}
paths=[]
for p in ROOT.rglob('*'):
    rel=p.relative_to(ROOT)
    if '.git' in rel.parts or '__pycache__' in rel.parts or p.name=='.DS_Store': continue
    if p.is_symlink(): raise ValueError('symlink in public tree: '+str(rel))
    if p.is_file() and rel.as_posix() not in excluded: paths.append(p)
paths.sort(key=lambda p:p.relative_to(ROOT).as_posix())
records=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,
          'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths]
manifest={'schema':'family173.manifest.v1','public_version':'1.0.1','files':records}
(ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
sums={x['path']:x['sha256'] for x in records}
sums['MANIFEST.json']=hashlib.sha256((ROOT/'MANIFEST.json').read_bytes()).hexdigest()
(ROOT/'SHA256SUMS').write_text(''.join(sums[n]+'  '+n+'\n' for n in sorted(sums)))
print(json.dumps({'event':'sealed','payload_files':len(records)},sort_keys=True))
