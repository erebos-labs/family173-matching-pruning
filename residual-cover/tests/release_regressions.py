"""Nonremovable controls for diagnostic checks and exact manifest inventory."""
from pathlib import Path
import copy,hashlib,json,os,shutil,subprocess,sys,tempfile,zipfile

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
import bounded_checks as b
import check_obstructions as o
import verify as v

def require(condition,message):
    if not condition:raise ValueError(message)

def rejected(name,action):
    try:action()
    except ValueError:return name
    raise ValueError('control was accepted: '+name)

def main():
    passed=[]
    old=b.dp_nu
    try:
        b.dp_nu=lambda *args:123
        passed.append(rejected('wrong_DP_oracle',b.primitive))
    finally:b.dp_nu=old
    old=o.boolean_product
    try:
        o.boolean_product=lambda *args:[[0]]
        passed.append(rejected('wrong_Boolean_obstruction',o.main))
    finally:o.boolean_product=old

    base=v.load(ROOT/'fixtures/repeated-H-positive.json')
    changes=[
        ('order_without_reproof',lambda q:q['request'].__setitem__('order',[1,0])),
        ('missing_prefix',lambda q:q['conversion']['selectors_Z'][0]['prefix_certificates'].pop()),
        ('wrong_block',lambda q:q['conversion']['selectors_Z'][0].__setitem__('coordinate',1)),
        ('missing_Gamma_cover',lambda q:q['accounting']['certificates']['Gamma']['cover'].pop()),
        ('wrong_branch',lambda q:q['conversion'].__setitem__('branch','all-Z'))]
    for name,mutate in changes:
        q=copy.deepcopy(base);mutate(q)
        passed.append(rejected(name,lambda:v.verify_record(q)))

    flags=['-B',*(['-O'] if sys.flags.optimize else [])]
    env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
    with tempfile.TemporaryDirectory(prefix='f173-release-controls-') as temporary:
        dest=Path(temporary)/'payload'
        shutil.copytree(ROOT,dest,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        def integrity(ok):
            run=subprocess.run([sys.executable,*flags,str(dest/'src/check_manifest.py')],
                env=env,text=True,capture_output=True)
            require((run.returncode==0)==ok,'unexpected manifest-check outcome: '+run.stdout+run.stderr)
        integrity(True)
        nested=dest/'examples/MANIFEST.sha256';nested.write_text('unlisted control\n')
        integrity(False);passed.append('unlisted_nested_manifest');nested.unlink()
        extra=dest/'examples/unlisted.txt';extra.write_text('unlisted control\n')
        integrity(False);passed.append('unlisted_ordinary_file');extra.unlink()
        note=dest/'NOTE.md';raw=note.read_bytes();note.write_bytes(raw+b'\nmutation\n')
        integrity(False);passed.append('changed_note');note.write_bytes(raw);integrity(True)

        # A nested manifest is an ordinary payload file when intentionally sealed.
        nested.write_text('listed control\n');target=Path(temporary)/'package.zip'
        subprocess.run([sys.executable,*flags,str(dest/'src/package.py'),'--output',str(target)],
            env=env,check=True,capture_output=True,text=True)
        rows=dict(line.split('  ',1)[::-1] for line in (dest/'MANIFEST.sha256').read_text().splitlines())
        require(rows.get('examples/MANIFEST.sha256')==hashlib.sha256(nested.read_bytes()).hexdigest(),
                'packager omitted nested manifest')
        with zipfile.ZipFile(target) as z:
            require(z.read('payload/examples/MANIFEST.sha256')==nested.read_bytes(),
                    'packager dropped nested manifest bytes')
        integrity(True);passed.append('listed_nested_manifest_packaged')
    print(json.dumps({'event':'release_regressions','status':'PASS','optimized':bool(sys.flags.optimize),
                      'controls':len(passed),'names':passed},sort_keys=True))

if __name__=='__main__':main()
