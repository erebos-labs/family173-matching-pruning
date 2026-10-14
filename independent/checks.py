#!/usr/bin/env python3
"""Audit-owned finite oracle; graph min-cover subset enumeration, no matching algorithm."""
import copy,itertools,json,random,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PKG=ROOT
sys.path.insert(0,str(PKG/'src'))
import construct,verify

def ck(v,msg):
    if not v: raise RuntimeError(msg)

def oracle(data):
    E=set(map(tuple,data['relation'])); R=list(map(tuple,data['R'])); C=list(map(tuple,data['C']))
    X=range(data['n'])
    conflict=lambda r,c:(r[0],c[0]) in E and (c[1],r[1]) in E
    Z={(i,j) for i,j in itertools.product(X,repeat=2)
       if any(r[1]==j and c[0]==i and conflict(r,c) for r in R for c in C)}
    H={(p,s) for p,s in itertools.product(X,repeat=2)
       if any(r[0]==p and c[1]==s and conflict(r,c) for r in R for c in C)}
    vl=lambda tag,p:f'{tag}:{p[0]}:{p[1]}'
    gs={
      'Gamma':({vl('R',r) for r in R}|{vl('ZL',z) for z in Z},
               {vl('C',c) for c in C}|{vl('ZR',z) for z in Z},set()),
      'B0':({vl('R',r) for r in R},{vl('H',h) for h in H},set()),
      'A0':({vl('H',h) for h in H},{vl('C',c) for c in C},set())}
    for r in R:
      for c in C:
        if conflict(r,c): gs['Gamma'][2].add((vl('R',r),vl('C',c)))
      for z in Z:
        if r[1]==z[1] and (r[0],z[0]) in E: gs['Gamma'][2].add((vl('R',r),vl('ZR',z)))
      for h in H:
        if r[0]==h[0] and (h[1],r[1]) in E: gs['B0'][2].add((vl('R',r),vl('H',h)))
    for c in C:
      for z in Z:
        if c[0]==z[0] and (c[1],z[1]) in E: gs['Gamma'][2].add((vl('ZL',z),vl('C',c)))
      for h in H:
        if h[1]==c[1] and (h[0],c[0]) in E: gs['A0'][2].add((vl('H',h),vl('C',c)))
    def cover(g):
      left,right,edges=g
      if len(left)>len(right): left,right,edges=right,left,{(v,u) for u,v in edges}
      left=list(left); best=len(left)
      for mask in range(1<<len(left)):
        selected={u for k,u in enumerate(left) if mask>>k&1}
        forced={v for u,v in edges if u not in selected}
        best=min(best,len(selected)+len(forced))
      return best
    sizes={k:cover(g) for k,g in gs.items()}
    isoR={r for r in R if not any(conflict(r,c) for c in C)}
    isoC={c for c in C if not any(conflict(r,c) for r in R)}
    best=10**9
    for mask in range(1<<(len(R)+len(C))):
      # mask denotes deleted vertices, unlike delivered retained-mask enumeration.
      rp={r for k,r in enumerate(R) if not mask>>k&1}
      cp={c for k,c in enumerate(C) if not mask>>(len(R)+k)&1}
      if not isoR<=rp or not isoC<=cp or any(conflict(r,c) for r in rp for c in cp): continue
      covered={z for z in Z if any(r[1]==z[1] and (r[0],z[0]) in E for r in rp)
               or any(c[0]==z[0] and (c[1],z[1]) in E for c in cp)}
      best=min(best,mask.bit_count()-len(Z-covered))
    cert=construct.construct(data)
    for k,g in gs.items():
      cg=cert['graphs'][k]
      ck(set(cg['left'])==g[0] and set(cg['right'])==g[1] and set(map(tuple,cg['edges']))==g[2],k+' support')
      ck(cg['size']==sizes[k],k+' cover oracle disagrees')
    ck(best==sizes['Gamma']-len(Z),'objective identity')
    ck(best==cert['pruning']['value'],'pruning optimum')
    ck(sizes['Gamma']<=len(Z)+min(sizes['B0'],sizes['A0']),'refined bound')
    verify.verify(data,cert)
    return len(gs)

counts=0
for n in range(3):
    pp=list(itertools.product(range(n),repeat=2))
    ss=[[list(p) for k,p in enumerate(pp) if mask>>k&1] for mask in range(1<<len(pp))]
    for E,R,C in itertools.product(ss,repeat=3):
      counts+=1; oracle(dict(schema='family173.instance.v1',n=n,relation=E,R=R,C=C))
rng=random.Random(173714)
for k in range(60):
    n=3; pp=list(itertools.product(range(n),repeat=2))
    data=dict(schema='family173.instance.v1',n=n,
      relation=[list(p) for p in pp if rng.random()<0.5],
      R=[list(p) for p in rng.sample(pp,rng.randrange(5))],
      C=[list(p) for p in rng.sample(pp,rng.randrange(5))])
    oracle(data)
stored=[]
for f in sorted((PKG/'examples').glob('*.instance.json')):
    d=json.loads(f.read_text()); c=json.loads(f.with_name(f.name.replace('.instance.','.certificate.')).read_text())
    verify.verify(d,c,brute=len(d['R'])+len(d['C'])<=12); stored.append(f.name)
print(json.dumps(dict(status='PASS',event='independent_oracle',exhaustive_inputs=counts,
 new_seeded_n3_inputs=60,min_cover_graph_optima=3*(counts+60),stored_certificates=len(stored)),sort_keys=True))
# Adversarial wrong-side, shared-endpoint, malformed-field cases beyond delivered tests.
d=json.loads((PKG/'examples/sharp_2x2.instance.json').read_text())
base=json.loads((PKG/'examples/sharp_2x2.certificate.json').read_text())
rejected=[]
mutations=[
 ('wrong_side_cover',lambda c:c['graphs']['Gamma']['cover_left'].__setitem__(0,'C:0:4')),
 ('negative_graph_size',lambda c:c['graphs']['B0'].__setitem__('size',-1)),
 ('bool_stats',lambda c:c['stats'].__setitem__('Z',True)),
 ('malformed_pruning',lambda c:c.__setitem__('pruning',None)),
 ('malformed_derived',lambda c:c.__setitem__('derived',None)),
 ('false_negative_objective',lambda c:c['pruning'].__setitem__('value',-1))]
for name,fn in mutations:
    c=copy.deepcopy(base);fn(c)
    with tempfile.TemporaryDirectory(prefix='family173-probes-') as td:
      out=Path(td)/'bad.json';out.write_text(json.dumps(c))
      r=subprocess.run([sys.executable,'-O',str(PKG/'src/verify.py'),str(PKG/'examples/sharp_2x2.instance.json'),str(out)],capture_output=True,text=True)
      ck(r.returncode!=0 and r.stderr.startswith('FAIL:'),name+' not cleanly rejected')
      rejected.append(dict(name=name,returncode=r.returncode,reason=r.stderr.strip()))
print(json.dumps(dict(status='PASS',event='extra_corruption_rejections',tests=rejected),sort_keys=True))
