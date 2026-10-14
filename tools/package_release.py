#!/usr/bin/env python3
"""Build a deterministic public ZIP from a verified manifest, outside the tree."""
import argparse,hashlib,json,subprocess,sys,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
VERSION='1.0.1'
NAME='family173-matching-pruning-v'+VERSION
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args()
out=args.output.resolve()
if out.is_relative_to(ROOT): ap.error('output must be outside the source tree')
out.mkdir(parents=True,exist_ok=True)
targets=[out/(NAME+'.zip'),out/'SHA256SUMS',out/'release-provenance.json']
if any(p.exists() for p in targets): ap.error('refusing to overwrite existing assets')
subprocess.run([sys.executable,str(ROOT/'verify_manifest.py')],cwd=ROOT,check=True)
records=json.loads((ROOT/'MANIFEST.json').read_text())['files']
names=[r['path'] for r in records]+['MANIFEST.json','SHA256SUMS']
with zipfile.ZipFile(targets[0],'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for name in sorted(names):
        info=zipfile.ZipInfo(NAME+'/'+name,(2026,10,14,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED
        info.external_attr=0o100644<<16
        z.writestr(info,(ROOT/name).read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
digest=hashlib.sha256(targets[0].read_bytes()).hexdigest()
try:
    commit=subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,check=True,capture_output=True,text=True).stdout.strip()
except (OSError,subprocess.CalledProcessError):
    commit=None
provenance={'schema':'family173.release-provenance.v1','version':VERSION,
  'repository':'https://github.com/erebos-labs/family173-matching-pruning',
  'release':'https://github.com/erebos-labs/family173-matching-pruning/releases/tag/v'+VERSION,
  'commit':commit,'package':{'name':targets[0].name,'bytes':targets[0].stat().st_size,'sha256':digest},
  'input_archive_sha256':'b2434d3008af12f7c7f4b0e495b8439cf25f36461987773752e6d79fc7118b83',
  'upstream_commit':'1581d4cbdd69a0faf34b2089614fe2a814316a6a',
  'scope':'Short structural corollary; novelty unestablished; no Lean or full Seymour endorsement.'}
targets[2].write_text(json.dumps(provenance,indent=2,sort_keys=True)+'\n')
sums={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (targets[0],targets[2])}
targets[1].write_text(''.join(sums[n]+'  '+n+'\n' for n in sorted(sums)))
print(json.dumps(provenance,sort_keys=True))
